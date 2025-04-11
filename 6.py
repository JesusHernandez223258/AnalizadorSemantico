import tkinter as tk
from tkinter import scrolledtext, messagebox, ttk
from lark import Lark, Transformer, v_args
from lark.exceptions import LarkError

# Gramática corregida
GRAMMAR = r"""
// Tokens
DECIMAL: /-?\d+\.\d+/
INTEGER: /-?\d+/
STRING: /"[^"]*"|'[^']*'/
IDENTIFIER: /[a-zA-Z_][a-zA-Z0-9_]*/
COMMENT: /\/\/.*/

// Ignora espacios en blanco y comentarios
%import common.WS
%ignore WS
%ignore COMMENT

// Reglas gramaticales
start: statement*

statement: var_decl
         | assignment
         | if_stmt
         | while_stmt
         | for_stmt
         | print_stmt
         | input_stmt
         | block
         | expr ";"

block: "{" statement* "}"

var_decl: "var" var_name ("=" expr)? ";"

var_name: IDENTIFIER

assignment: IDENTIFIER "=" expr ";"

if_stmt: "if" "(" expr ")" statement ("else" statement)?

while_stmt: "while" "(" expr ")" statement

for_stmt: "for" "(" (var_decl | assignment | ";") expr? ";" expr? ")" statement

print_stmt: "print" "(" expr ("," expr)* ")" ";"

input_stmt: "input" "(" IDENTIFIER ")" ";"

expr: comparison

comparison: sum_expr (("==" | "!=" | "<" | ">" | "<=" | ">=") sum_expr)*

sum_expr: mul_expr (("+" | "-") mul_expr)*

mul_expr: unary (("*" | "/") unary)*

unary: ("+" | "-") unary -> unary_op
     | primary

primary: DECIMAL -> decimal
       | INTEGER -> integer
       | STRING -> string
       | "true" -> true_value
       | "false" -> false_value
       | IDENTIFIER -> identifier
       | "(" expr ")" -> parenthesized
"""

class SymbolTable:
    def __init__(self):
        self.scopes = [{}]
    
    def enter_scope(self):
        self.scopes.append({})
    
    def exit_scope(self):
        if len(self.scopes) > 1:
            self.scopes.pop()
    
    def declare(self, name, var_type, value=None):
        if name in self.scopes[-1]:
            raise Exception(f"Variable '{name}' ya declarada")
        self.scopes[-1][name] = {'type': var_type, 'value': value}
    
    def lookup(self, name):
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        raise Exception(f"Variable '{name}' no declarada")
    
    def assign(self, name, value):
        for scope in reversed(self.scopes):
            if name in scope:
                scope[name]['value'] = value
                return
        raise Exception(f"Variable '{name}' no declarada")

@v_args(inline=True)
class SemanticAnalyzer(Transformer):
    def __init__(self):
        self.symbol_table = SymbolTable()
        self.output = []
        super().__init__()
    
    def start(self, *statements):
        return [stmt for stmt in statements if stmt is not None]
    
    def var_name(self, token):
        # Extract the variable name from the token
        return token.value
    
    def var_decl(self, *args):
        # Handle variable declaration
        if len(args) == 2:  # var identifier = expr;
            name, value = args
        elif len(args) == 1:  # var identifier;
            name = args[0]
            value = None
        else:
            raise Exception(f"Formato incorrecto para declaración de variable: {args}")
        
        var_type = type(value).__name__ if value is not None else "None"
        self.symbol_table.declare(name, var_type, value)
        return ('declare', name, value)
    
    def assignment(self, *args):
        # Handle assignment
        if len(args) == 2:  # identifier = expr;
            identifier, expr = args
            
            # Get the name from the identifier
            if isinstance(identifier, str):
                name = identifier
            else:
                name = identifier.value if hasattr(identifier, 'value') else str(identifier)
            
            try:
                # Try to look up the variable
                self.symbol_table.lookup(name)
                # If found, assign the new value
                self.symbol_table.assign(name, expr)
                return ('assign', name, expr)
            except Exception as e:
                # Re-raise the exception with more context
                raise Exception(f"Error en asignación '{name} = {expr}': {str(e)}")
        else:
            raise Exception(f"Formato incorrecto para asignación: {args}")
    
    def if_stmt(self, *args):
        # Handle already transformed nodes
        if len(args) == 3:  # condition, then_stmt, else_stmt
            condition, then_stmt, else_stmt = args
            # Validar que la condición sea booleana o pueda ser interpretada como tal
            self._validate_condition(condition)
            return ('if', condition, then_stmt, else_stmt)
        elif len(args) == 2:  # condition, then_stmt
            condition, then_stmt = args
            # Validar que la condición sea booleana o pueda ser interpretada como tal
            self._validate_condition(condition)
            return ('if', condition, then_stmt, None)
        else:
            raise Exception(f"Formato incorrecto para if: {args}")

    def _validate_condition(self, condition):
        """Valida que una condición sea de tipo booleano o comparable"""
        # Si es una expresión, validar según el operador
        if isinstance(condition, tuple) and len(condition) >= 3:
            op = condition[0]
            # Los operadores de comparación generan expresiones booleanas
            if op in ["==", "!=", "<", ">", "<=", ">="]:
                return True

        # Si es un valor simple, verificar su tipo
        if isinstance(condition, str) and not (condition == "true" or condition == "false"):
            # Si es un identificador, verificar su tipo en la tabla de símbolos
            try:
                var_info = self.symbol_table.lookup(condition)
                if var_info['type'] in ['str', 'string']:
                    raise Exception(f"Error semántico: la condición '{condition}' es de tipo cadena y no puede ser usada como condición booleana")
                if var_info['type'] not in ['bool', 'int', 'float']:
                    raise Exception(f"Error semántico: la condición '{condition}' no es de tipo booleano")
            except Exception as e:
                if "no declarada" not in str(e):
                    raise e
                else:
                    # Si la variable no está declarada, es un error
                    raise Exception(f"Error semántico: la variable '{condition}' no está declarada")

        # Tipos literales
        if isinstance(condition, str) and not (condition == "true" or condition == "false"):
            raise Exception(f"Error semántico: '{condition}' no es una condición booleana válida")

        return True

    def while_stmt(self, *args):
        # Handle already transformed nodes
        if len(args) == 2:  # condition, body
            condition, body = args
            # Validar que la condición sea booleana o pueda ser interpretada como tal
            self._validate_condition(condition)
            return ('while', condition, body)
        else:
            raise Exception(f"Formato incorrecto para while: {args}")
    
    def for_stmt(self, *args):
        # Handle already transformed nodes
        if len(args) == 4:  # init, cond, update, body
            init, cond, update, body = args
            return ('for', init, cond, update, body)
        else:
            # Handle other cases if needed
            raise Exception(f"Formato incorrecto para for: {args}")
    
    def print_stmt(self, *args):
        # All args are expressions to print
        self.output.append(f"Imprimiendo: {' '.join(str(x) for x in args)}")
        return ('print', *args)
    
    def input_stmt(self, identifier):
        # Handle already transformed node
        name = identifier.value if hasattr(identifier, 'value') else str(identifier)
        return ('input', name)
    
    def block(self, *statements):
        # Don't create a new scope for blocks
        return ('block', *statements)
    
    def expr(self, expr):
        return expr
    
    def comparison(self, left, *args):
        result = left
        i = 0
        while i < len(args):
            if isinstance(args[i], str) and args[i] in ["==", "!=", "<", ">", "<=", ">="]:
                if i + 1 < len(args):
                    op, right = args[i], args[i+1]
                    result = (op, result, right)
                    i += 2
                else:
                    break
            else:
                i += 1
        return result
    
    def sum_expr(self, left, *args):
        result = left
        i = 0
        while i < len(args):
            if isinstance(args[i], str) and args[i] in ["+", "-"]:
                if i + 1 < len(args):
                    op, right = args[i], args[i+1]
                    result = (op, result, right)
                    i += 2
                else:
                    break
            else:
                i += 1
        return result
    
    def mul_expr(self, left, *args):
        result = left
        i = 0
        while i < len(args):
            if isinstance(args[i], str) and args[i] in ["*", "/"]:
                if i + 1 < len(args):
                    op, right = args[i], args[i+1]
                    result = (op, result, right)
                    i += 2
                else:
                    break
            else:
                i += 1
        return result
    
    def unary_op(self, op, expr):
        if op == '-':
            if isinstance(expr, (int, float)):
                return -expr
            return ('neg', expr)
        return expr
    
    def parenthesized(self, expr):
        return expr
    
    def decimal(self, token):
        return float(token.value)
    
    def integer(self, token):
        return int(token.value)
    
    def string(self, token):
        # Eliminar comillas
        return token.value[1:-1]
    
    def true_value(self):
        return True
    
    def false_value(self):
        return False
    
    def identifier(self, token):
        name = token.value
        try:
            var_info = self.symbol_table.lookup(name)
            return var_info['value']
        except Exception:
            # Just return the name for now
            return name

class AnalyzerApp:
    def __init__(self, root):
        self.root = root
        self.setup_ui()
        self.parser = Lark(GRAMMAR, start='start', parser='lalr')
    
    def setup_ui(self):
        self.root.title("Analizador Léxico-Sintáctico-Semántico")
        self.root.geometry("1000x800")
        
        # Main panel
        main_panel = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_panel.pack(fill=tk.BOTH, expand=True)
        
        # Input panel
        input_frame = ttk.Frame(main_panel, padding=10)
        main_panel.add(input_frame)
        
        ttk.Label(input_frame, text="Código Fuente:").pack(anchor=tk.W)
        self.input_text = scrolledtext.ScrolledText(
            input_frame, width=60, height=30, font=('Consolas', 10))
        self.input_text.pack(fill=tk.BOTH, expand=True)
        
        # Output panel
        output_frame = ttk.Frame(main_panel, padding=10)
        main_panel.add(output_frame)
        
        self.notebook = ttk.Notebook(output_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        
        # Create tabs
        self.create_tab("Tokens", 15)
        self.create_tab("Árbol", 15)
        self.create_tab("Símbolos", 15)
        self.create_tab("Salida", 10)
        
        # Buttons
        button_frame = ttk.Frame(input_frame)
        button_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(button_frame, text="Analizar", command=self.analyze).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Ejemplo", command=self.load_example).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Limpiar", command=self.clear).pack(side=tk.LEFT, padx=5)
    
    def create_tab(self, title, height):
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text=title)
        text = scrolledtext.ScrolledText(
            frame, width=80, height=height, font=('Consolas', 10))
        text.pack(fill=tk.BOTH, expand=True)
        setattr(self, f"{title.lower()}_text", text)
    
    def analyze(self):
        code = self.input_text.get("1.0", tk.END)
        
        # Clear previous results
        for tab in ['tokens', 'árbol', 'símbolos', 'salida']:
            getattr(self, f"{tab}_text").delete("1.0", tk.END)
        
        try:
            # Lexical and syntactic analysis
            tree = self.parser.parse(code)
            
            # Show tokens
            tokens = list(self.parser.lex(code))
            self.tokens_text.insert(tk.END, "TOKENS:\n\n")
            for token in tokens:
                self.tokens_text.insert(tk.END, f"{token.type:<15} {token.value}\n")
            
            # Show parse tree
            self.árbol_text.insert(tk.END, "ÁRBOL SINTÁCTICO:\n\n")
            self.árbol_text.insert(tk.END, tree.pretty())
            
            # Semantic analysis
            transformer = SemanticAnalyzer()
            ast = transformer.transform(tree)
            
            # Show symbol table
            self.símbolos_text.insert(tk.END, "TABLA DE SÍMBOLOS:\n\n")
            self.símbolos_text.insert(tk.END, "Ámbito   | Nombre  | Tipo    | Valor\n")
            self.símbolos_text.insert(tk.END, "---------|---------|---------|--------\n")
            for scope_idx, scope in enumerate(transformer.symbol_table.scopes):
                scope_name = f"Scope {scope_idx}" if scope_idx > 0 else "Global"
                for name, info in scope.items():
                    self.símbolos_text.insert(
                        tk.END, f"{scope_name:<9} | {name:<7} | {info['type']:<7} | {info['value']}\n")
            
            # Show output
            self.salida_text.insert(tk.END, "RESULTADO:\n\n")
            for output in transformer.output:
                self.salida_text.insert(tk.END, output + "\n")
            
            messagebox.showinfo("Éxito", "Análisis completado correctamente")
        
        except Exception as e:
            messagebox.showerror("Error", str(e))
            import traceback
            traceback.print_exc()
    
    def load_example(self):
        example = """// Programa de ejemplo
var x = 10;
var y = 20.5;
var nombre = "Juan";
var activo = true;

print("Resultado:", x + y);

if (x > 5) {
    print("x es mayor que 5");
} else {
    print("x no es mayor que 5");
}

var i = 0;
while (i < 3) {
    print("Iteración:", i);
    i = i + 1;
}"""
        self.clear()
        self.input_text.insert(tk.END, example)
    
    def clear(self):
        self.input_text.delete("1.0", tk.END)
        for tab in ['tokens', 'árbol', 'símbolos', 'salida']:
            getattr(self, f"{tab}_text").delete("1.0", tk.END)

# Add a debug function to help diagnose issues
def debug_parse(code):
    parser = Lark(GRAMMAR, start='start', parser='lalr')
    print("Parsing code...")
    tree = parser.parse(code)
    print("Parse tree:")
    print(tree.pretty())
    
    print("\nTransforming tree...")
    transformer = SemanticAnalyzer()
    try:
        ast = transformer.transform(tree)
        print("Transformation successful!")
        print("Symbol table:")
        for scope_idx, scope in enumerate(transformer.symbol_table.scopes):
            scope_name = f"Scope {scope_idx}" if scope_idx > 0 else "Global"
            for name, info in scope.items():
                print(f"{scope_name}: {name} = {info}")
        print("\nOutput:")
        for output in transformer.output:
            print(output)
    except Exception as e:
        print(f"Transformation failed: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    # Test the fix with the problematic code
#     test_code = """
# var i = 0;
# while (i < 3) {
#     print("Iteración:", i);
#     i = i + 1;
# }
# """
#     debug_parse(test_code)
    
    # Uncomment to run the GUI
    root = tk.Tk()
    app = AnalyzerApp(root)
    root.mainloop()
