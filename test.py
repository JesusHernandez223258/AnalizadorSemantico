import tkinter as tk
from tkinter import scrolledtext, messagebox, ttk
# Asegúrate de importar Token
from lark import Lark, Transformer, v_args, Token
from lark.exceptions import LarkError
import traceback # Para mejor depuración de errores

# --- Gramática MODIFICADA ---
# Define la estructura sintáctica del lenguaje a analizar.
GRAMMAR = r"""
    // --- Tokens (Unidades léxicas básicas) ---
    // Números
    DECIMAL.2: /-?\d+\.\d+/ // Prioridad 2 para floats
    INTEGER.1: /-?\d+/      // Prioridad 1 para ints

    // Cadenas de texto
    STRING: /"[^"]*"|'[^']*'/

    // Identificadores (Nombres de variables)
    IDENTIFIER: /[a-zA-Z_][a-zA-Z0-9_]*/

    // Palabras clave
    VAR: "var"
    IF: "if"
    ELSE: "else"
    WHILE: "while"
    FOR: "for"
    PRINT: "print"
    INPUT: "input"
    TRUE: "true"
    FALSE: "false"

    // Operadores (Definidos explícitamente)
    PLUS: "+"
    MINUS: "-"
    STAR: "*"
    SLASH: "/"
    ASSIGN_OP: "=" // Renombrado para evitar confusión con EQ
    EQ: "=="
    NEQ: "!="
    LT: "<"
    GT: ">"
    LTE: "<="
    GTE: ">="
    LPAR: "("
    RPAR: ")"
    LBRACE: "{"
    RBRACE: "}"
    SEMICOLON: ";"
    COMMA: ","


    // Comentarios (estilo C++)
    COMMENT: /\/\/.*/

    // --- Ignorar Espacios y Comentarios ---
    %import common.WS
    %ignore WS
    %ignore COMMENT

    // --- Reglas Gramaticales (Usando tokens explícitos) ---
    start: statement*

    ?statement: var_decl
             | assignment
             | if_stmt
             | while_stmt
             | for_stmt
             | print_stmt
             | input_stmt
             | block
             | expr SEMICOLON -> expr_stmt // Expresión como sentencia

    block: LBRACE statement* RBRACE

    var_decl: VAR IDENTIFIER (ASSIGN_OP expr)? SEMICOLON

    assignment: IDENTIFIER ASSIGN_OP expr SEMICOLON

    if_stmt: IF LPAR expr RPAR statement (ELSE statement)?

    while_stmt: WHILE LPAR expr RPAR statement

    # Simplificado - NO se usan helpers _no_semi, se parsea directamente
    for_stmt: FOR LPAR (var_decl | assignment | SEMICOLON) expr? SEMICOLON expr? RPAR statement

    print_stmt: PRINT LPAR [expr (COMMA expr)*] RPAR SEMICOLON

    input_stmt: INPUT LPAR IDENTIFIER RPAR SEMICOLON

    // --- Expresiones (Usando tokens explícitos) ---
    ?expr: comparison

    ?comparison: sum_expr ((EQ | NEQ | LT | GT | LTE | GTE) sum_expr)*

    ?sum_expr: mul_expr ((PLUS | MINUS) mul_expr)*

    ?mul_expr: unary ((STAR | SLASH) unary)*

    ?unary: (PLUS | MINUS) unary -> unary_op
          | primary

    ?primary: DECIMAL         -> number
            | INTEGER         -> number
            | STRING          -> string
            | TRUE            -> true_value
            | FALSE           -> false_value
            | IDENTIFIER      -> identifier
            | LPAR expr RPAR  -> parenthesized

"""

# --- Tabla de Símbolos (Sin cambios respecto a la versión funcional anterior) ---
class SymbolTable:
    def __init__(self):
        self.scopes = [{}]
    def enter_scope(self): self.scopes.append({})
    def exit_scope(self):
        if len(self.scopes) > 1: self.scopes.pop()
    def declare(self, name, var_type, value=None):
        current_scope = self.scopes[-1]
        if name in current_scope: raise Exception(f"Error Semántico: La variable '{name}' ya ha sido declarada en este ámbito.")
        current_scope[name] = {'type': var_type, 'value': value}
        print(f"[SymbolTable] Declarada: {name} (Tipo: {var_type}, Valor: {value})")
    def lookup(self, name):
        for scope in reversed(self.scopes):
            if name in scope: return scope[name]
        raise Exception(f"Error Semántico: La variable '{name}' no ha sido declarada.")
    def assign(self, name, value):
        for scope in reversed(self.scopes):
            if name in scope:
                new_type = self._get_value_type(value)
                scope[name]['value'] = value; scope[name]['type'] = new_type
                print(f"[SymbolTable] Asignada: {name} = {value} (Nuevo Tipo: {new_type})")
                return
        raise Exception(f"Error Semántico: Intento de asignar a variable no declarada '{name}'.")
    def _get_value_type(self, value):
        if isinstance(value, bool): return 'bool'
        if isinstance(value, int): return 'int'
        if isinstance(value, float): return 'float'
        if isinstance(value, str): return 'string'
        # Podríamos necesitar manejar ('assign', ...) u otros nodos AST si la evaluación fuera más compleja
        return type(value).__name__
    def __str__(self):
        output = "--- Tabla de Símbolos ---\n"; i = 0
        for scope in self.scopes:
            output += f"Ámbito {i}:\n"; i += 1
            if not scope: output += "  (vacío)\n"
            else:
                for name, info in scope.items(): output += f"  - {name}: Tipo={info.get('type', '?')}, Valor={info.get('value', '?')}\n"
        output += "-------------------------"
        return output

# --- Analizador Semántico (LIMPIO Y CORREGIDO) ---
class SemanticAnalyzer(Transformer):
    def __init__(self):
        self.symbol_table = SymbolTable()
        self.output = []
        print("Analizador Semántico Inicializado.")
        super().__init__()

    # --- Métodos (Reciben 'children' como lista) ---

    def start(self, children): return ('program', *children)

    def var_decl(self, children):
        # len=3: [Token VAR, Token IDENTIFIER, Token SEMICOLON]
        # len=5: [Token VAR, Token IDENTIFIER, Token ASSIGN_OP, expr_result, Token SEMICOLON]
        if len(children) == 3: name_token = children[1]; value = None
        elif len(children) == 5: name_token = children[1]; value = children[3]
        else: raise ValueError(f"Estructura inesperada var_decl (len {len(children)}): {children}")
        name = name_token.value
        value_type = self.symbol_table._get_value_type(value)
        self.symbol_table.declare(name, value_type, value)
        return ('declare', name, value)

    def assignment(self, children):
        # children: [Token IDENTIFIER, Token ASSIGN_OP, expr_result, Token SEMICOLON]
        if len(children) != 4: raise ValueError(f"Estructura inesperada assignment: {children}")
        name_token = children[0]; value = children[2]
        name = name_token.value
        self.symbol_table.lookup(name)
        self.symbol_table.assign(name, value)
        return ('assign', name, value)

    # --- CORREGIDO: if_stmt ---
    def if_stmt(self, children):
        # children (no else): [Token IF, Token LPAR, expr_result, Token RPAR, stmt_result] (len 5)
        # children (con else): [Token IF, Token LPAR, expr_result, Token RPAR, stmt_result, Token ELSE, stmt_result] (len 7)
        if len(children) == 5:
            condition = children[2] # Índice correcto para expr_result
            then_stmt = children[4] # Índice correcto para stmt_result (then)
            else_stmt = None
        elif len(children) == 7:
            condition = children[2]
            then_stmt = children[4]
            # children[5] es Token ELSE
            else_stmt = children[6] # Índice correcto para stmt_result (else)
        else:
            raise ValueError(f"Estructura inesperada if_stmt (len {len(children)}): {children}")

        print(f"[Semantic Check] Analizando IF: Condición={condition}")
        self._validate_condition(condition) # Ahora recibe el resultado correcto
        return ('if', condition, then_stmt, else_stmt)

    def while_stmt(self, children):
        # children: [Token WHILE, Token LPAR, expr_result, Token RPAR, body_result] (len 5)
        if len(children) != 5: raise ValueError(f"Estructura inesperada while_stmt: {children}")
        condition = children[2] # Índice correcto
        body = children[4]      # Índice correcto
        print(f"[Semantic Check] Analizando WHILE: Condición={condition}")
        self._validate_condition(condition)
        return ('while', condition, body)

    def for_stmt(self, children):
         # children: [Token FOR, Token LPAR, init_result, cond_result, Token SEMI, update_result, Token RPAR, body_result]
         # La estructura real aquí es compleja debido a las opciones en init. ¡Requiere depuración!
         print(f"[Semantic Check] Analizando FOR (simplificado - children: {len(children)})")
         # Asignaciones básicas para evitar crash, índices probablemente incorrectos
         init = children[2] if len(children)>2 else None
         cond = children[3] if len(children)>3 else None # <-- Necesita ajuste seguro
         update = children[5] if len(children)>5 else None # <-- Necesita ajuste seguro
         body = children[7] if len(children)>7 else None # <-- Necesita ajuste seguro
         return ('for', init, cond, update, body)

    # --- CORREGIDO: print_stmt ---
    def print_stmt(self, children):
        # children: [Token PRINT, Token LPAR, expr1?, Token COMMA?, expr2?, ..., Token RPAR, Token SEMICOLON]
        # Simplemente filtramos todos los Tokens para quedarnos con los resultados de expr
        expressions_to_print = [child for child in children if not isinstance(child, Token)]
        output_str = " ".join(map(str, expressions_to_print))
        self.output.append(output_str)
        print(f"[Runtime Simulation] Print: {output_str}")
        return ('print', *expressions_to_print)

    def input_stmt(self, children):
         # children: [Token INPUT, Token LPAR, Token IDENTIFIER, Token RPAR, Token SEMICOLON] (len 5)
         if len(children) != 5: raise ValueError(f"Estructura inesperada input_stmt: {children}")
         name_token = children[2] # Índice correcto
         name = name_token.value
         self.symbol_table.lookup(name)
         self.symbol_table.assign(name, "[Input Placeholder]")
         print(f"[Semantic Check/Runtime Sim] Input para: {name}")
         return ('input', name)

    def block(self, children): return ('block', *children)
    def expr_stmt(self, children):
        # children: [expr_result, Token SEMICOLON]
        print(f"[Semantic Check] Expresión como sentencia: {children[0]}")
        return ('expr_stmt', children[0])


    # --- Expresiones ---
    def identifier(self, children):
        name_token = children[0]
        name = name_token.value
        var_info = self.symbol_table.lookup(name)
        # Advertencia si se usa antes de asignar (podría causar el 'None' en comparison)
        if var_info.get('value', '__MISSING__') is None: # Usamos .get() para seguridad
             print(f"Advertencia Semántica: Variable '{name}' usada posiblemente antes de tener un valor asignado.")
        return var_info.get('value') # Devolvemos valor (o None si no inicializada)

    def _validate_condition(self, condition_value):
        if not isinstance(condition_value, bool):
            raise Exception(f"Error Semántico: Condición ({condition_value}, tipo {type(condition_value).__name__}) no es bool.")
        print(f"[Semantic Check] Condición válida: {condition_value}")
        return condition_value

    def _binary_op(self, op_str, left, right):
        # Añadimos manejo básico de None para evitar errores tempranos, aunque idealmente no debería ocurrir
        # si el chequeo de 'identifier' fuera más estricto o devolviera un error.
        if left is None or right is None:
             print(f"Advertencia: Operando es None en '{left} {op_str} {right}'")
             # Podríamos intentar una evaluación permisiva o lanzar error
             # Por ahora, intentemos continuar si es comparación, falla si es aritmética
             if op_str in ['+', '-', '*', '/']:
                  raise TypeError(f"Error Semántico: Operando None en operación aritmética '{left} {op_str} {right}'")
             # Para comparaciones, Python maneja None == algo, None != algo
             # Pero None < algo, None > algo fallará

        print(f"[Expression Eval] Calculando: {left} {op_str} {right}")
        if not isinstance(op_str, str): raise TypeError(f"Error Interno: _binary_op op_str no es string: {op_str}")
        is_arithmetic = op_str in ['+', '-', '*', '/']
        is_comparison = op_str in ['==', '!=', '<', '>', '<=', '>=']
        if is_arithmetic:
            if not isinstance(left, (int, float)) or not isinstance(right, (int, float)):
                raise Exception(f"Error Semántico: Op. aritmética '{op_str}' requiere números (recibió {type(left).__name__}, {type(right).__name__}).")
            if op_str == '/' and isinstance(right, (int, float)) and right == 0:
                raise ZeroDivisionError("Error Semántico: División por cero.")
        elif is_comparison:
             # Permitir comparar None con otros (produce False excepto para ==/!=)
             if left is not None and right is not None:
                 if type(left) != type(right) and not (isinstance(left,(int,float)) and isinstance(right,(int,float))):
                     if not (isinstance(left, bool) and isinstance(right, bool)) and \
                        not (isinstance(left, str) and isinstance(right, str)):
                        print(f"Advertencia: Comparando tipos diferentes ({type(left).__name__}, {type(right).__name__}) con '{op_str}'.")
        try:
            # Evaluación estándar de Python
            if op_str == '+': return left + right
            if op_str == '-': return left - right
            if op_str == '*': return left * right
            if op_str == '/': return left / right
            if op_str == '==': return left == right
            if op_str == '!=': return left != right
            # Comparaciones pueden fallar con None
            if op_str == '<': return left < right
            if op_str == '>': return left > right
            if op_str == '<=': return left <= right
            if op_str == '>=': return left >= right
        except TypeError as e: raise Exception(f"Error de Tipo en '{left} {op_str} {right}': {e}")
        raise Exception(f"Operador binario '{op_str}' no implementado")

    def comparison(self, children): return self._process_binary_expr_chain_no_inline(children)
    def sum_expr(self, children): return self._process_binary_expr_chain_no_inline(children)
    def mul_expr(self, children): return self._process_binary_expr_chain_no_inline(children)

    # --- CORREGIDO: _process_binary_expr_chain_no_inline ---
    def _process_binary_expr_chain_no_inline(self, children):
        """Procesa cadena binaria SIN v_args(inline=True), manejando lista plana."""
        # children puede ser:
        # 1. [operand] (len 1)
        # 2. [operand1, op_token1, operand2, op_token2, operand3, ...] (len >= 3 y impar)

        if len(children) == 1:
            # Caso base: solo un operando
            return children[0]

        elif len(children) >= 3 and (len(children) % 2) != 0:
            # Caso cadena plana: [op1, tok1, op2, tok2, op3, ...]
            result = children[0]  # Empezar con el primer operando
            i = 1
            while i < len(children):
                op_token = children[i]
                right_operand = children[i+1]

                # Verificaciones de tipos internos
                if not isinstance(op_token, Token):
                    raise TypeError(f"Error Interno: Se esperaba Token como operador en la posición {i}: {children}")
                # (No necesitamos verificar right_operand aquí, _binary_op lo hará)

                op_string = op_token.value
                result = self._binary_op(op_string, result, right_operand)
                i += 2 # Avanzar al siguiente operador
            return result

        else:
            # Si no es len 1, o no es len >= 3 e impar, la estructura es inesperada
            raise TypeError(f"Error Interno: Estructura desconocida para expr chain (len {len(children)}): {children}")

    def unary_op(self, children):
        # children: [Token(op), unary_result]
        op_token = children[0]; value = children[1]
        op_str = op_token.value
        if op_str == '-':
            if not isinstance(value, (int, float)): raise Exception(f"Error Semántico: Op. unario '-' requiere número.")
            return -value
        return value

    # Primitivos (Sin cambios respecto a la v3)
    def number(self, children):
        token = children[0]
        if not isinstance(token, Token): raise TypeError(f"Error Interno: 'number' esperaba Token, recibió {token}")
        value_str = token.value
        if '.' in value_str: return float(value_str)
        return int(value_str)

    def string(self, children):
        token = children[0]
        if not isinstance(token, Token): raise TypeError(f"Error Interno: 'string' esperaba Token, recibió {token}")
        return token.value[1:-1]

    def true_value(self, children): return True
    def false_value(self, children): return False
    def parenthesized(self, children):
        # children: [Token LPAR, expr_result, Token RPAR]
        return children[1]

# --- Interfaz Gráfica (Tkinter - SIN CAMBIOS) ---
class AnalyzerApp:
    def __init__(self, root):
        self.root = root
        try:
            # IMPORTANTE: Instanciar Lark SIN parser='lalr' si quitamos @v_args(inline=True)
            #             O dejarlo si queremos LALR pero manejamos hijos manualmente.
            #             LALR es generalmente preferido por eficiencia. Lo dejamos.
            self.parser = Lark(GRAMMAR, start='start', parser='lalr', propagate_positions=True)
            print("Parser LALR creado con éxito.")
        except Exception as e:
            messagebox.showerror("Error de Gramática", f"No se pudo crear el parser:\n{e}\n\nVerifica la definición de GRAMMAR.")
            print(traceback.format_exc())
            self.parser = None
        self.setup_ui()

    # ... (resto de la clase AnalyzerApp sin cambios) ...
    def setup_ui(self):
        self.root.title("Analizador Léxico-Sintáctico-Semántico (Lenguaje Simple)")
        self.root.geometry("1000x800")
        main_panel = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_panel.pack(fill=tk.BOTH, expand=True)
        input_frame = ttk.Frame(main_panel, padding=10)
        main_panel.add(input_frame, weight=1)
        ttk.Label(input_frame, text="Código Fuente:").pack(anchor=tk.W)
        self.input_text = scrolledtext.ScrolledText(input_frame, width=60, height=30, font=('Consolas', 11), wrap=tk.WORD)
        self.input_text.pack(fill=tk.BOTH, expand=True)
        button_frame = ttk.Frame(input_frame)
        button_frame.pack(fill=tk.X, pady=5)
        ttk.Button(button_frame, text="Analizar", command=self.analyze, state=tk.NORMAL if self.parser else tk.DISABLED).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Ejemplo", command=self.load_example).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Limpiar", command=self.clear).pack(side=tk.LEFT, padx=5)
        output_frame = ttk.Frame(main_panel, padding=10)
        main_panel.add(output_frame, weight=1)
        self.notebook = ttk.Notebook(output_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        self.tabs = {}
        tab_titles = ["Tokens", "Árbol Sintáctico", "Tabla Símbolos", "Salida (Print)", "Errores"]
        for title in tab_titles:
            frame = ttk.Frame(self.notebook)
            self.notebook.add(frame, text=title)
            text_area = scrolledtext.ScrolledText(frame, width=80, height=15, font=('Consolas', 10), wrap=tk.WORD, state=tk.DISABLED)
            text_area.pack(fill=tk.BOTH, expand=True)
            self.tabs[title] = text_area
    def _clear_output_tabs(self):
        for text_area in self.tabs.values():
            text_area.config(state=tk.NORMAL); text_area.delete("1.0", tk.END); text_area.config(state=tk.DISABLED)
    def _write_to_tab(self, tab_title, content):
         if tab_title in self.tabs:
            text_area = self.tabs[tab_title]; text_area.config(state=tk.NORMAL)
            text_area.insert(tk.END, content + "\n"); text_area.config(state=tk.DISABLED)
         else: print(f"Advertencia: Pestaña inexistente '{tab_title}'")
    def analyze(self):
        if not self.parser: messagebox.showerror("Error", "Parser no inicializado."); return
        code = self.input_text.get("1.0", tk.END); self._clear_output_tabs()
        try:
            tokens = list(self.parser.lex(code)); self._write_to_tab("Tokens", "--- TOKENS ---")
            for token in tokens:
                 if token.type != 'WS': self._write_to_tab("Tokens", f"Tipo: {token.type:<15} Valor: {repr(token.value):<25} Línea: {token.line}, Col: {token.column}")
            self._write_to_tab("Tokens", "\nAnálisis Léxico completado.")
            parse_tree = self.parser.parse(code); self._write_to_tab("Árbol Sintáctico", "--- ÁRBOL SINTÁCTICO (Parse Tree) ---")
            self._write_to_tab("Árbol Sintáctico", parse_tree.pretty()); self._write_to_tab("Árbol Sintáctico", "\nAnálisis Sintáctico completado.")
            self._write_to_tab("Tabla Símbolos", "--- ANÁLISIS SEMÁNTICO ---")

            # IMPORTANTE: Instanciar SemanticAnalyzer SIN @v_args(inline=True) global
            # Si quitamos el decorador de la clase, hay que instanciarla normal
            semantic_analyzer = SemanticAnalyzer() # <--- Sin decorador arriba

            abstract_syntax_tree = semantic_analyzer.transform(parse_tree) # Ejecuta análisis
            self._write_to_tab("Tabla Símbolos", str(semantic_analyzer.symbol_table)); self._write_to_tab("Tabla Símbolos", "\nAnálisis Semántico completado.")
            self._write_to_tab("Salida (Print)", "--- SALIDA SIMULADA (PRINT) ---")
            if not semantic_analyzer.output: self._write_to_tab("Salida (Print)", "(No hubo salida por 'print')")
            else:
                for line in semantic_analyzer.output: self._write_to_tab("Salida (Print)", line)
            messagebox.showinfo("Éxito", "Análisis completado sin errores detectados."); self._write_to_tab("Errores", "No se detectaron errores.")
        except LarkError as e:
            error_msg = f"Error de Sintaxis/Léxico:\n{e}"; messagebox.showerror("Error de Análisis", error_msg)
            self._write_to_tab("Errores", error_msg); print(traceback.format_exc())
        except ZeroDivisionError as e:
            error_msg = f"Error Semántico (División por Cero):\n{e}"; messagebox.showerror("Error Semántico", error_msg)
            self._write_to_tab("Errores", error_msg); print(traceback.format_exc())
        except Exception as e:
            error_msg = f"Error (posiblemente Semántico):\n{e}"; messagebox.showerror("Error Durante el Análisis", error_msg)
            self._write_to_tab("Errores", error_msg); print("--- TRACEBACK COMPLETO DEL ERROR ---"); print(traceback.format_exc()); print("------------------------------------")
    def load_example(self): example = """
// --- Programa de Ejemplo ---

// Declaraciones de variables
var a = 10;
var b = 20.5;
var nombre = "Mundo";
var valido = true;

var c = a + 5;

print("Hola, ", nombre, "!");
print("Suma:", a + b);
print("C vale:", c);

// Condicionales
if (a > 5) {
    print("A es mayor que 5");
} else {
    print("A no es mayor que 5");
}

if (valido) {
    print("Es válido");
}

if (c == 15) {
    print("C es 15");
}

// Expresión con operadores
var r = 1 + 2 * 3 - 4 / 2;
print("Resultado:", r);

// Bucle while
var i = 0;
while (i < 3) {
    print("Contador:", i);
    i = i + 1;
}

print("Fin del programa.");
// --- Fin del Programa de Ejemplo ---
"""; self.clear(); self.input_text.insert("1.0", example.strip())
    def clear(self): self.input_text.delete("1.0", tk.END); self._clear_output_tabs()


# --- Punto de Entrada ---
if __name__ == "__main__":
    root = tk.Tk(); app = AnalyzerApp(root); root.mainloop()