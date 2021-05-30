// Copyright 2020 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package source

import (
	"bytes"
	"context"
	"fmt"
	"go/ast"
	"go/doc"
	"go/printer"
	"go/token"
	"go/types"
	"strings"

	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/internal/event"
	"golang.org/x/tools/internal/lsp/debug/tag"
	"golang.org/x/tools/internal/lsp/protocol"
)

// FormatType returns the detail and kind for a types.Type.
func FormatType(typ types.Type, qf types.Qualifier) (detail string, kind protocol.CompletionItemKind) {
	if types.IsInterface(typ) {
		detail = "interface{...}"
		kind = protocol.InterfaceCompletion
	} else if _, ok := typ.(*types.Struct); ok {
		detail = "struct{...}"
		kind = protocol.StructCompletion
	} else if typ != typ.Underlying() {
		detail, kind = FormatType(typ.Underlying(), qf)
	} else {
		detail = types.TypeString(typ, qf)
		kind = protocol.ClassCompletion
	}
	return detail, kind
}

type signature struct {
	name, doc        string
	params, results  []string
	variadic         bool
	needResultParens bool
}

func fieldName(x ast.Expr) *ast.Ident {
	switch t := x.(type) {
	case *ast.Ident:
		return t
	case *ast.SelectorExpr:
		if _, ok := t.X.(*ast.Ident); ok {
			return t.Sel
		}
	case *ast.StarExpr:
		return fieldName(t.X)
	}
	return nil
}

func filterIdentList(list []*ast.Ident, f func(name string) bool) []*ast.Ident {
	j := 0
	for _, x := range list {
		if f(x.Name) {
			list[j] = x
			j++
		}
	}
	return list[0:j]
}

func cloneAST(original ast.Node) ast.Node {
	m := make(map[ast.Node]ast.Node)
	astutil.Apply(original, nil, func(c *astutil.Cursor) bool {
		switch node := c.Node().(type) {
		case nil:
			// No-op.
		case *ast.ArrayType:
			m[node] = &ast.ArrayType{
				Lbrack: node.Lbrack,
				Len:    exprFromMap(m, node.Len),
				Elt:    exprFromMap(m, node.Elt),
			}
		case *ast.BasicLit:
			m[node] = &ast.BasicLit{
				ValuePos: node.ValuePos,
				Kind:     node.Kind,
				Value:    node.Value,
			}
		case *ast.ChanType:
			m[node] = &ast.ChanType{
				Begin: node.Begin,
				Arrow: node.Arrow,
				Dir:   node.Dir,
				Value: exprFromMap(m, node.Value),
			}
		case *ast.Comment:
			m[node] = &ast.Comment{
				Slash: node.Slash,
				Text:  node.Text,
			}
		case *ast.CommentGroup:
			cg := new(ast.CommentGroup)
			if node.List != nil {
				cg.List = make([]*ast.Comment, len(node.List))
				for i := range node.List {
					cg.List[i] = m[node.List[i]].(*ast.Comment)
				}
			}
			m[node] = cg
		case *ast.Field:
			m[node] = &ast.Field{
				Doc:     commentGroupFromMap(m, node.Doc),
				Names:   copyIdentList(m, node.Names),
				Type:    exprFromMap(m, node.Type),
				Tag:     basicLitFromMap(m, node.Tag),
				Comment: commentGroupFromMap(m, node.Comment),
			}
		case *ast.FieldList:
			fl := &ast.FieldList{
				Opening: node.Opening,
				Closing: node.Closing,
			}
			if node.List != nil {
				fl.List = make([]*ast.Field, len(node.List))
				for i := range node.List {
					fl.List[i] = m[node.List[i]].(*ast.Field)
				}
			}
			m[node] = fl
		case *ast.FuncType:
			m[node] = &ast.FuncType{
				Func:    node.Func,
				Params:  fieldListFromMap(m, node.Params),
				Results: fieldListFromMap(m, node.Results),
			}
		case *ast.Ident:
			// Keep identifiers the same identity so they can be conveniently
			// used with the original *types.Info.
			m[node] = node
		case *ast.InterfaceType:
			m[node] = &ast.InterfaceType{
				Interface:  node.Interface,
				Methods:    fieldListFromMap(m, node.Methods),
				Incomplete: node.Incomplete,
			}
		case *ast.MapType:
			m[node] = &ast.MapType{
				Map:   node.Map,
				Key:   exprFromMap(m, node.Key),
				Value: exprFromMap(m, node.Value),
			}
		case *ast.StarExpr:
			m[node] = &ast.StarExpr{
				Star: node.Star,
				X:    exprFromMap(m, node.X),
			}
		case *ast.StructType:
			m[node] = &ast.StructType{
				Struct:     node.Struct,
				Fields:     fieldListFromMap(m, node.Fields),
				Incomplete: node.Incomplete,
			}
		default:
			panic(fmt.Sprintf("unhandled AST node: %T", node))
		}
		return true
	})
	return m[original]
}

func commentGroupFromMap(m map[ast.Node]ast.Node, key *ast.CommentGroup) *ast.CommentGroup {
	if key == nil {
		return nil
	}
	return m[key].(*ast.CommentGroup)
}

func exprFromMap(m map[ast.Node]ast.Node, key ast.Expr) ast.Expr {
	if key == nil {
		return nil
	}
	return m[key].(ast.Expr)
}

func fieldListFromMap(m map[ast.Node]ast.Node, key *ast.FieldList) *ast.FieldList {
	if key == nil {
		return nil
	}
	return m[key].(*ast.FieldList)
}

func basicLitFromMap(m map[ast.Node]ast.Node, key *ast.BasicLit) *ast.BasicLit {
	if key == nil {
		return nil
	}
	return m[key].(*ast.BasicLit)
}

func copyIdentList(m map[ast.Node]ast.Node, idents []*ast.Ident) []*ast.Ident {
	if idents == nil {
		return nil
	}
	newIdents := make([]*ast.Ident, len(idents))
	for i := range idents {
		newIdents[i] = m[idents[i]].(*ast.Ident)
	}
	return newIdents
}

func filterStructType(x ast.Node) (ast.Node, bool) {
	if _, ok := x.(*ast.StructType); !ok {
		return x, false // not a struct
	}

	c := cloneAST(x)
	filter := func(name string) bool { return ast.IsExported(name) }
	ast.Inspect(c, func(c ast.Node) bool {
		s, ok := c.(*ast.StructType)
		if !ok {
			return true
		}

		fields := s.Fields
		if fields == nil {
			return true
		}

		j := 0
		list := fields.List

		for _, f := range list {
			keepField := false
			if len(f.Names) == 0 {
				// anonymous field
				name := fieldName(f.Type)
				keepField = name != nil && filter(name.Name)
			} else {
				f.Names = filterIdentList(f.Names, filter)
				keepField = len(f.Names) > 0
			}
			if keepField {
				list[j] = f
				j++
			}
		}

		fields.List = list[0:j]
		return true
	})

	return c, true
}

func (s *signature) Format() string {
	var b strings.Builder
	b.WriteByte('(')
	for i, p := range s.params {
		if i > 0 {
			b.WriteString(", ")
		}
		b.WriteString(p)
	}
	b.WriteByte(')')

	// Add space between parameters and results.
	if len(s.results) > 0 {
		b.WriteByte(' ')
	}
	if s.needResultParens {
		b.WriteByte('(')
	}
	for i, r := range s.results {
		if i > 0 {
			b.WriteString(", ")
		}
		b.WriteString(r)
	}
	if s.needResultParens {
		b.WriteByte(')')
	}
	return b.String()
}

func (s *signature) Params() []string {
	return s.params
}

// NewBuiltinSignature returns signature for the builtin object with a given
// name, if a builtin object with the name exists.
func NewBuiltinSignature(ctx context.Context, s Snapshot, name string) (*signature, error) {
	builtin, err := s.BuiltinFile(ctx)
	if err != nil {
		return nil, err
	}
	obj := builtin.File.Scope.Lookup(name)
	if obj == nil {
		return nil, fmt.Errorf("no builtin object for %s", name)
	}
	decl, ok := obj.Decl.(*ast.FuncDecl)
	if !ok {
		return nil, fmt.Errorf("no function declaration for builtin: %s", name)
	}
	if decl.Type == nil {
		return nil, fmt.Errorf("no type for builtin decl %s", decl.Name)
	}
	var variadic bool
	if decl.Type.Params.List != nil {
		numParams := len(decl.Type.Params.List)
		lastParam := decl.Type.Params.List[numParams-1]
		if _, ok := lastParam.Type.(*ast.Ellipsis); ok {
			variadic = true
		}
	}
	params, _ := formatFieldList(ctx, s, decl.Type.Params, variadic)
	results, needResultParens := formatFieldList(ctx, s, decl.Type.Results, false)
	d := decl.Doc.Text()
	switch s.View().Options().HoverKind {
	case SynopsisDocumentation:
		d = doc.Synopsis(d)
	case NoDocumentation:
		d = ""
	}
	return &signature{
		doc:              d,
		name:             name,
		needResultParens: needResultParens,
		params:           params,
		results:          results,
		variadic:         variadic,
	}, nil
}

var replacer = strings.NewReplacer(
	`ComplexType`, `complex128`,
	`FloatType`, `float64`,
	`IntegerType`, `int`,
)

func formatFieldList(ctx context.Context, snapshot Snapshot, list *ast.FieldList, variadic bool) ([]string, bool) {
	if list == nil {
		return nil, false
	}
	var writeResultParens bool
	var result []string
	for i := 0; i < len(list.List); i++ {
		if i >= 1 {
			writeResultParens = true
		}
		p := list.List[i]
		cfg := printer.Config{Mode: printer.UseSpaces | printer.TabIndent, Tabwidth: 4}
		b := &bytes.Buffer{}
		if err := cfg.Fprint(b, snapshot.FileSet(), p.Type); err != nil {
			event.Error(ctx, "unable to print type", nil, tag.Type.Of(p.Type))
			continue
		}
		typ := replacer.Replace(b.String())
		if len(p.Names) == 0 {
			result = append(result, typ)
		}
		for _, name := range p.Names {
			if name.Name != "" {
				if i == 0 {
					writeResultParens = true
				}
				result = append(result, fmt.Sprintf("%s %s", name.Name, typ))
			} else {
				result = append(result, typ)
			}
		}
	}
	if variadic {
		result[len(result)-1] = strings.Replace(result[len(result)-1], "[]", "...", 1)
	}
	return result, writeResultParens
}

// NewSignature returns formatted signature for a types.Signature struct.
func NewSignature(ctx context.Context, s Snapshot, pkg Package, sig *types.Signature, comment *ast.CommentGroup, qf types.Qualifier) *signature {
	params := make([]string, 0, sig.Params().Len())
	for i := 0; i < sig.Params().Len(); i++ {
		el := sig.Params().At(i)
		typ := FormatVarType(ctx, s, pkg, el, qf)
		p := typ
		if el.Name() != "" {
			p = el.Name() + " " + typ
		}
		params = append(params, p)
	}
	var needResultParens bool
	results := make([]string, 0, sig.Results().Len())
	for i := 0; i < sig.Results().Len(); i++ {
		if i >= 1 {
			needResultParens = true
		}
		el := sig.Results().At(i)
		typ := FormatVarType(ctx, s, pkg, el, qf)
		if el.Name() == "" {
			results = append(results, typ)
		} else {
			if i == 0 {
				needResultParens = true
			}
			results = append(results, el.Name()+" "+typ)
		}
	}
	var d string
	if comment != nil {
		d = comment.Text()
	}
	switch s.View().Options().HoverKind {
	case SynopsisDocumentation:
		d = doc.Synopsis(d)
	case NoDocumentation:
		d = ""
	}
	return &signature{
		doc:              d,
		params:           params,
		results:          results,
		variadic:         sig.Variadic(),
		needResultParens: needResultParens,
	}
}

// FormatVarType formats a *types.Var, accounting for type aliases.
// To do this, it looks in the AST of the file in which the object is declared.
// On any errors, it always fallbacks back to types.TypeString.
func FormatVarType(ctx context.Context, snapshot Snapshot, srcpkg Package, obj *types.Var, qf types.Qualifier) string {
	pkg, err := FindPackageFromPos(ctx, snapshot, obj.Pos())
	if err != nil {
		return types.TypeString(obj.Type(), qf)
	}

	expr, err := varType(ctx, snapshot, pkg, obj)
	if err != nil {
		return types.TypeString(obj.Type(), qf)
	}

	// The type names in the AST may not be correctly qualified.
	// Determine the package name to use based on the package that originated
	// the query and the package in which the type is declared.
	// We then qualify the value by cloning the AST node and editing it.
	clonedInfo := make(map[token.Pos]*types.PkgName)
	qualified := cloneExpr(expr, pkg.GetTypesInfo(), clonedInfo)

	// If the request came from a different package than the one in which the
	// types are defined, we may need to modify the qualifiers.
	qualified = qualifyExpr(qualified, srcpkg, pkg, clonedInfo, qf)
	fmted := FormatNode(snapshot.FileSet(), qualified)
	return fmted
}

// varType returns the type expression for a *types.Var.
func varType(ctx context.Context, snapshot Snapshot, pkg Package, obj *types.Var) (ast.Expr, error) {
	field, err := snapshot.PosToField(ctx, pkg, obj.Pos())
	if err != nil {
		return nil, err
	}
	if field == nil {
		return nil, fmt.Errorf("no declaration for object %s", obj.Name())
	}
	typ, ok := field.Type.(ast.Expr)
	if !ok {
		return nil, fmt.Errorf("unexpected type for node (%T)", field.Type)
	}
	return typ, nil
}

// qualifyExpr applies the "pkgName." prefix to any *ast.Ident in the expr.
func qualifyExpr(expr ast.Expr, srcpkg, pkg Package, clonedInfo map[token.Pos]*types.PkgName, qf types.Qualifier) ast.Expr {
	ast.Inspect(expr, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.ArrayType, *ast.ChanType, *ast.Ellipsis,
			*ast.FuncType, *ast.MapType, *ast.ParenExpr,
			*ast.StarExpr, *ast.StructType:
			// These are the only types that are cloned by cloneExpr below,
			// so these are the only types that we can traverse and potentially
			// modify. This is not an ideal approach, but it works for now.
			return true
		case *ast.SelectorExpr:
			// We may need to change any selectors in which the X is a package
			// name and the Sel is exported.
			x, ok := n.X.(*ast.Ident)
			if !ok {
				return false
			}
			obj, ok := clonedInfo[x.Pos()]
			if !ok {
				return false
			}
			x.Name = qf(obj.Imported())
			return false
		case *ast.Ident:
			if srcpkg == pkg {
				return false
			}
			// Only add the qualifier if the identifier is exported.
			if ast.IsExported(n.Name) {
				pkgName := qf(pkg.GetTypes())
				n.Name = pkgName + "." + n.Name
			}
		}
		return false
	})
	return expr
}

// cloneExpr only clones expressions that appear in the parameters or return
// values of a function declaration. The original expression may be returned
// to the caller in 2 cases:
//    (1) The expression has no pointer fields.
//    (2) The expression cannot appear in an *ast.FuncType, making it
//        unnecessary to clone.
// This function also keeps track of selector expressions in which the X is a
// package name and marks them in a map along with their type information, so
// that this information can be used when rewriting the expression.
//
// NOTE: This function is tailored to the use case of qualifyExpr, and should
// be used with caution.
func cloneExpr(expr ast.Expr, info *types.Info, clonedInfo map[token.Pos]*types.PkgName) ast.Expr {
	switch expr := expr.(type) {
	case *ast.ArrayType:
		return &ast.ArrayType{
			Lbrack: expr.Lbrack,
			Elt:    cloneExpr(expr.Elt, info, clonedInfo),
			Len:    expr.Len,
		}
	case *ast.ChanType:
		return &ast.ChanType{
			Arrow: expr.Arrow,
			Begin: expr.Begin,
			Dir:   expr.Dir,
			Value: cloneExpr(expr.Value, info, clonedInfo),
		}
	case *ast.Ellipsis:
		return &ast.Ellipsis{
			Ellipsis: expr.Ellipsis,
			Elt:      cloneExpr(expr.Elt, info, clonedInfo),
		}
	case *ast.FuncType:
		return &ast.FuncType{
			Func:    expr.Func,
			Params:  cloneFieldList(expr.Params, info, clonedInfo),
			Results: cloneFieldList(expr.Results, info, clonedInfo),
		}
	case *ast.Ident:
		return cloneIdent(expr)
	case *ast.MapType:
		return &ast.MapType{
			Map:   expr.Map,
			Key:   cloneExpr(expr.Key, info, clonedInfo),
			Value: cloneExpr(expr.Value, info, clonedInfo),
		}
	case *ast.ParenExpr:
		return &ast.ParenExpr{
			Lparen: expr.Lparen,
			Rparen: expr.Rparen,
			X:      cloneExpr(expr.X, info, clonedInfo),
		}
	case *ast.SelectorExpr:
		s := &ast.SelectorExpr{
			Sel: cloneIdent(expr.Sel),
			X:   cloneExpr(expr.X, info, clonedInfo),
		}
		if x, ok := expr.X.(*ast.Ident); ok && ast.IsExported(expr.Sel.Name) {
			if obj, ok := info.ObjectOf(x).(*types.PkgName); ok {
				clonedInfo[s.X.Pos()] = obj
			}
		}
		return s
	case *ast.StarExpr:
		return &ast.StarExpr{
			Star: expr.Star,
			X:    cloneExpr(expr.X, info, clonedInfo),
		}
	case *ast.StructType:
		return &ast.StructType{
			Struct:     expr.Struct,
			Fields:     cloneFieldList(expr.Fields, info, clonedInfo),
			Incomplete: expr.Incomplete,
		}
	default:
		return expr
	}
}

func cloneFieldList(fl *ast.FieldList, info *types.Info, clonedInfo map[token.Pos]*types.PkgName) *ast.FieldList {
	if fl == nil {
		return nil
	}
	if fl.List == nil {
		return &ast.FieldList{
			Closing: fl.Closing,
			Opening: fl.Opening,
		}
	}
	list := make([]*ast.Field, 0, len(fl.List))
	for _, f := range fl.List {
		var names []*ast.Ident
		for _, n := range f.Names {
			names = append(names, cloneIdent(n))
		}
		list = append(list, &ast.Field{
			Comment: f.Comment,
			Doc:     f.Doc,
			Names:   names,
			Tag:     f.Tag,
			Type:    cloneExpr(f.Type, info, clonedInfo),
		})
	}
	return &ast.FieldList{
		Closing: fl.Closing,
		Opening: fl.Opening,
		List:    list,
	}
}

func cloneIdent(ident *ast.Ident) *ast.Ident {
	return &ast.Ident{
		NamePos: ident.NamePos,
		Name:    ident.Name,
		Obj:     ident.Obj,
	}
}
