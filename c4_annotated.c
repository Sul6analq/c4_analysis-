// c4.c - C in four functions

// char, int, and pointer types
// if, while, return, and expression statements
// just enough features to allow self-compilation and a bit more

// Written by Robert Swierczek
// Annotated by Sultan Alqassab
#include <stdio.h> // standard I/O functions
#include <stdlib.h> // standard library functions
#include <memory.h> // memory manipulation functions
#include <unistd.h> // access to the POSIX OS API
#include <fcntl.h> // File control options
#define int long long // 64-bit integer for avoiding overflow
//Global integers
char *p, *lp, // current position in source code and last processed line
     *data;   // data/bss pointer

int *e, *le,  // current position in emitted code
    *id,      // currently parsed identifier
    *sym,     // symbol table (simple list of identifiers)
    tk,       // current token
    ival,     // current token value
    ty,       // current expression type
    loc,      // local variable offset
    line,     // current line number
    src,      // print source and assembly flag
    debug;    // print executed instructions

// tokens and classes (operators last and in precedence order)
enum {
  Num = 128, Fun, Sys, Glo, Loc, Id, // Basic token types
  Char, Else, Enum, If, Int, Return, Sizeof, While, // Keywords supported in C4
  Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak // Operators ordered by precedence
};

// opcodes - low-level instructions executed by the VM
enum { LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,
       OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,
       OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT };

// data types
enum { CHAR, INT, PTR };

// identifier offsets (since we can't create an ident struct)
enum { Tk, Hash, Name, Class, Type, Val, HClass, HType, HVal, Idsz };

void next() //Lexical Analyzer (Reads the source code character by character and generates tokens)
{
  char *pp; //store staring position of an identifier

  while (tk = *p) { // Read the current characte
    ++p;
    if (tk == '\n') { // Handle new line character
      if (src) {
        printf("%d: %.*s", line, p - lp, lp); / Print current source line if `src` flag is enabled
        lp = p;
        while (le < e) { // Print assembly instructions if enabled
          printf("%8.4s", &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
                           "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
                           "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[*++le * 5]);
          if (*le <= ADJ) printf(" %d\n", *++le); else printf("\n");
        }
      }
      ++line; // Increase the line counter
    }
    else if (tk == '#') { // Skip preprocessor directives
      while (*p != 0 && *p != '\n') ++p;
    }
    else if ((tk >= 'a' && tk <= 'z') || (tk >= 'A' && tk <= 'Z') || tk == '_') { // Identifier handling
      pp = p - 1;
      while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9') || *p == '_')
        tk = tk * 147 + *p++;
      tk = (tk << 6) + (p - pp);
      id = sym;
      while (id[Tk]) { // Search for identifier in the symbol table.
        if (tk == id[Hash] && !memcmp((char *)id[Name], pp, p - pp)) { tk = id[Tk]; return; }
        id = id + Idsz;
      }
      id[Name] = (int)pp;
      id[Hash] = tk;
      tk = id[Tk] = Id;
      return;
    }
    // Process numeric literals
    else if (tk >= '0' && tk <= '9') {
      if (ival = tk - '0') { while (*p >= '0' && *p <= '9') ival = ival * 10 + *p++ - '0'; } // Decimal number: consume subsequent digits
      else if (*p == 'x' || *p == 'X') { // Hexadecimal literal: process hex digits.
        while ((tk = *++p) && ((tk >= '0' && tk <= '9') || (tk >= 'a' && tk <= 'f') || (tk >= 'A' && tk <= 'F')))
          ival = ival * 16 + (tk & 15) + (tk >= 'A' ? 9 : 0);
      }
      else { while (*p >= '0' && *p <= '7') ival = ival * 8 + *p++ - '0'; }  // Octal literal
      tk = Num; // mark the token as a number literal
      return;
    }
    else if (tk == '/') { // Handle the '/' character: either division or start of a comment
      if (*p == '/') { 
        ++p; // consume the second '/'
        while (*p != 0 && *p != '\n') ++p; // skip the rest of the line (comment)
      }
      else {
        tk = Div; // division operator
        return;
      }
    }
    else if (tk == '\'' || tk == '"') { // Process character and string literals
      pp = data; // point to the current position in the data segment
      while (*p != 0 && *p != tk) {
        if ((ival = *p++) == '\\') { // handle escape sequences
          if ((ival = *p++) == 'n') ival = '\n';
        }
        if (tk == '"') *data++ = ival; // for string literals, store the character in the data segment
      }
      ++p; // skip the closing quote
    // for strings, ival is the address of the string
      if (tk == '"') ival = (int)pp; else tk = Num; // for character literals, treat as a number
      return;
    }
    else if (tk == '=') { if (*p == '=') { ++p; tk = Eq; } else tk = Assign; return; } // Handle '=' and '==' operators
    else if (tk == '+') { if (*p == '+') { ++p; tk = Inc; } else tk = Add; return; } // Handle '+' and '++' operators
    else if (tk == '-') { if (*p == '-') { ++p; tk = Dec; } else tk = Sub; return; } // Handle '-' and '--' operators
    else if (tk == '!') { if (*p == '=') { ++p; tk = Ne; } return; } // Handle '!' and '!=' operators
    else if (tk == '<') { if (*p == '=') { ++p; tk = Le; } else if (*p == '<') { ++p; tk = Shl; } else tk = Lt; return; } // Handle '<', '<=', and '<<' operators
    else if (tk == '>') { if (*p == '=') { ++p; tk = Ge; } else if (*p == '>') { ++p; tk = Shr; } else tk = Gt; return; } // Handle '>', '>=', and '>>' operators
    else if (tk == '|') { if (*p == '|') { ++p; tk = Lor; } else tk = Or; return; } // Handle '|' and '||' operators
    else if (tk == '&') { if (*p == '&') { ++p; tk = Lan; } else tk = And; return; }// Handle '&' and '&&' operators
    else if (tk == '^') { tk = Xor; return; } // bitwise XOR operator
    else if (tk == '%') { tk = Mod; return; } // modulus operator
    else if (tk == '*') { tk = Mul; return; }  // multiplication operator
    else if (tk == '[') { tk = Brak; return; } // array subscript operator
    else if (tk == '?') { tk = Cond; return; } // conditional operator
        // Characters that represent themselves: '~', ';', '{', '}', '(', ')', ']', ',', ':'
    else if (tk == '~' || tk == ';' || tk == '{' || tk == '}' || tk == '(' || tk == ')' || tk == ']' || tk == ',' || tk == ':') return;
  }
}

// This function parses an expression from the source code using a recursive descent
// method combined with "precedence climbing" to handle operator precedence.
void expr(int lev)
{
  int t, *d;

  if (!tk) { printf("%d: unexpected eof in expression\n", line); exit(-1); }  // Check for an unexpected end-of-file while parsing an expression.
  else if (tk == Num) {   // Handle a numeric literal 
    *++e = IMM;       // Emit an immediate instruction.
    *++e = ival;      // The literal value.
    next();           // Move to the next token.
    ty = INT;         // Set expression type to int. 
  } 
  else if (tk == '"') { // Handle a string literal
    *++e = IMM;       // Load the address of the string.
    *++e = ival;      // ival contains the address of the string in the data area.
    next();           // Consume the string literal.
    while (tk == '"') next(); // Skip consecutive string tokens
    data = (char *)((int)data + sizeof(int) & -sizeof(int)); // Align the data pointer to an integer boundary
    ty = PTR;         // The result is a pointer.
  }
  else if (tk == Sizeof) { // Handle the sizeof operator
    next(); if (tk == '(') next(); else { printf("%d: open paren expected in sizeof\n", line); exit(-1); }
    ty = INT; // Default type is int 
    if (tk == Int) next(); else if (tk == Char) { next(); ty = CHAR; }
    while (tk == Mul) { next(); ty = ty + PTR; }// Handle pointer indirection for sizeof
    if (tk == ')') next(); else { printf("%d: close paren expected in sizeof\n", line); exit(-1); }
    // Emit the size of the type 
    *++e = IMM; *++e = (ty == CHAR) ? sizeof(char) : sizeof(int);
    ty = INT; // The result of sizeof is always an int
  }
  else if (tk == Id) { // Handle identifiers
    d = id; // Save the current identifier pointer
    next(); // Consume the identifier
    if (tk == '(') { // Function call
      next(); // Consume '('
      t = 0; // Parameter count.
      // Parse function arguments.
      while (tk != ')') { 
        expr(Assign);   // Parse an argument expression.
        *++e = PSH;     // Push the argument onto the stack.
        ++t;
        if (tk == ',') next(); }
      next(); // Consume ')'
      if (d[Class] == Sys) *++e = d[Val]; // System function call
      else if (d[Class] == Fun) { 
          *++e = JSR; // Jump to subroutine
          *++e = d[Val]; // Address of the function}
      else { printf("%d: bad function call\n", line); exit(-1); }
      if (t) { *++e = ADJ; *++e = t; } // Adjust the stack if there are arguments
      ty = d[Type]; // Set the expression type to the function's return type
    }
    else if (d[Class] == Num) { *++e = IMM; *++e = d[Val]; ty = INT; } // If the identifier represents a constant
    else { // For variables, load their address based on their storage class
      if (d[Class] == Loc) { *++e = LEA; *++e = loc - d[Val]; } // Local variable: calculate offset
      else if (d[Class] == Glo) { *++e = IMM; *++e = d[Val]; }  // Global variable: load absolute address
      else { printf("%d: undefined variable\n", line); exit(-1); }
      *++e = ((ty = d[Type]) == CHAR) ? LC : LI; // Load the value from the variable
    }
  }
  else if (tk == '(') { // Handle parenthesized expressions or casts
    next(); // Consume '('
    if (tk == Int || tk == Char) {
    // This is a type cast
      t = (tk == Int) ? INT : CHAR; next();
    // Handle pointer casts
      while (tk == Mul) { next(); t = t + PTR; }
      if (tk == ')') next(); else { printf("%d: bad cast\n", line); exit(-1); }
      expr(Inc); // Parse the expression being cast
      ty = t; // Set the type to the cast type
    }
    else {
      expr(Assign); // Grouped expression
      if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    }
  }
  else if (tk == Mul) { // Handle pointer dereference operator '*'
    next(); expr(Inc); // Parse the expression after '*'
    if (ty > INT) ty = ty - PTR; else { printf("%d: bad dereference\n", line); exit(-1); }
    *++e = (ty == CHAR) ? LC : LI; // Load a char or int from the memory address
  }
  else if (tk == And) { // Handle address-of operator '&'
    next(); expr(Inc); 
    // Ensure that the operand is a valid lvalue
    if (*e == LC || *e == LI) --e; else { printf("%d: bad address-of\n", line); exit(-1); }
    ty = ty + PTR; // The result type is a pointer
  }
// Handle logical NOT '!' operator
  else if (tk == '!') { next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = 0; *++e = EQ; ty = INT; }
// Handle bitwise NOT '~' operator
  else if (tk == '~') { next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = -1; *++e = XOR; ty = INT; }
// Handle unary plus '+'
  else if (tk == Add) { next(); expr(Inc); ty = INT; }
// Handle unary minus '-'
  else if (tk == Sub) {
    next(); *++e = IMM;
    if (tk == Num) { *++e = -ival; next(); } else { *++e = -1; *++e = PSH; expr(Inc); *++e = MUL; }
    ty = INT;
  }
// Handle pre-increment '++' and pre-decrement '--'
  else if (tk == Inc || tk == Dec) {
    t = tk; next(); expr(Inc); 
    // Verify that the operand is a valid lvalue
    if (*e == LC) { *e = PSH; *++e = LC; }
    else if (*e == LI) { *e = PSH; *++e = LI; }
    else { printf("%d: bad lvalue in pre-increment\n", line); exit(-1); }
    *++e = PSH;
    *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
    *++e = (t == Inc) ? ADD : SUB;
    *++e = (ty == CHAR) ? SC : SI;
  }
  else { printf("%d: bad expression\n", line); exit(-1); }
// After handling a primary expression, process binary operators using precedence climbing
  while (tk >= lev) { // "precedence climbing" or "Top Down Operator Precedence" method
    t = ty; // Save the current type before processing the operator
    if (tk == Assign) {
      next();
      if (*e == LC || *e == LI) *e = PSH; else { printf("%d: bad lvalue in assignment\n", line); exit(-1); }
      expr(Assign); *++e = ((ty = t) == CHAR) ? SC : SI;
    }
    else if (tk == Cond) {
      next();
      *++e = BZ; d = ++e;
      expr(Assign);
      if (tk == ':') next(); else { printf("%d: conditional missing colon\n", line); exit(-1); }
      *d = (int)(e + 3); *++e = JMP; d = ++e;
      expr(Cond);
      *d = (int)(e + 1);
    }
    else if (tk == Lor) { next(); *++e = BNZ; d = ++e; expr(Lan); *d = (int)(e + 1); ty = INT; }
    else if (tk == Lan) { next(); *++e = BZ;  d = ++e; expr(Or);  *d = (int)(e + 1); ty = INT; }
    else if (tk == Or)  { next(); *++e = PSH; expr(Xor); *++e = OR;  ty = INT; }
    else if (tk == Xor) { next(); *++e = PSH; expr(And); *++e = XOR; ty = INT; }
    else if (tk == And) { next(); *++e = PSH; expr(Eq);  *++e = AND; ty = INT; }
    else if (tk == Eq)  { next(); *++e = PSH; expr(Lt);  *++e = EQ;  ty = INT; }
    else if (tk == Ne)  { next(); *++e = PSH; expr(Lt);  *++e = NE;  ty = INT; }
    else if (tk == Lt)  { next(); *++e = PSH; expr(Shl); *++e = LT;  ty = INT; }
    else if (tk == Gt)  { next(); *++e = PSH; expr(Shl); *++e = GT;  ty = INT; }
    else if (tk == Le)  { next(); *++e = PSH; expr(Shl); *++e = LE;  ty = INT; }
    else if (tk == Ge)  { next(); *++e = PSH; expr(Shl); *++e = GE;  ty = INT; }
    else if (tk == Shl) { next(); *++e = PSH; expr(Add); *++e = SHL; ty = INT; }
    else if (tk == Shr) { next(); *++e = PSH; expr(Add); *++e = SHR; ty = INT; }
    else if (tk == Add) {
      next(); *++e = PSH; expr(Mul);
      if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL;  }
      *++e = ADD;
    }
    else if (tk == Sub) {
      next(); *++e = PSH; expr(Mul);
      if (t > PTR && t == ty) { *++e = SUB; *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = DIV; ty = INT; }
      else if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL; *++e = SUB; }
      else *++e = SUB;
    }
    else if (tk == Mul) { next(); *++e = PSH; expr(Inc); *++e = MUL; ty = INT; }
    else if (tk == Div) { next(); *++e = PSH; expr(Inc); *++e = DIV; ty = INT; }
    else if (tk == Mod) { next(); *++e = PSH; expr(Inc); *++e = MOD; ty = INT; }
    else if (tk == Inc || tk == Dec) {
      if (*e == LC) { *e = PSH; *++e = LC; }
      else if (*e == LI) { *e = PSH; *++e = LI; }
      else { printf("%d: bad lvalue in post-increment\n", line); exit(-1); }
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
      *++e = (tk == Inc) ? ADD : SUB;
      *++e = (ty == CHAR) ? SC : SI;
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
      *++e = (tk == Inc) ? SUB : ADD;
      next();
    }
    else if (tk == Brak) {
      next(); *++e = PSH; expr(Assign);
      if (tk == ']') next(); else { printf("%d: close bracket expected\n", line); exit(-1); }
      if (t > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL;  }
      else if (t < PTR) { printf("%d: pointer type expected\n", line); exit(-1); }
      *++e = ADD;
      *++e = ((ty = t - PTR) == CHAR) ? LC : LI;
    }
    else { printf("%d: compiler error tk=%d\n", line, tk); exit(-1); }
  }
}
// This function parses a statement from the source code and emits the corresponding code.
// It handles control flow constructs like 'if', 'while', 'return', blocks
void stmt()
{
  int *a, *b; // 'a' and 'b' are used to hold jump addresses for control flow

  if (tk == If) {
    next(); // consume 'if'
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign); // parse the if condition
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; // emit branch if zero 
    b = ++e;  // reserve space for jump address for the false branch
    stmt(); // parse the 'then' statement
    if (tk == Else) {
      *b = (int)(e + 3);  // fix up the false branch jump address
      *++e = JMP;         // jump over the else branch
      b = ++e;            // reserve space for jump address for end of else
      next();             // consume 'else'
      stmt();             // parse the else statement
    }
    *b = (int)(e + 1);  // fix up the jump address to point to code after the if/else statement
  }
  else if (tk == While) {
    next();  // consume 'while'
    a = e + 1;  // record the address at the beginning of the loop condition
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);  // parse the loop condition
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ;  // branch if the condition is false (exit loop)
    b = ++e;  // reserve space for jump address for loop exit
    stmt();   // parse the loop body
    *++e = JMP; *++e = (int)a;  // jump back to the beginning of the loop
    *b = (int)(e + 1);  // fix up the exit branch jump address
  }
  else if (tk == Return) {
    next();  // consume 'return'
    if (tk != ';') expr(Assign);  // if there is a return value, parse it
    *++e = LEV;  // emit leave instruction to exit the function
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
  else if (tk == '{') {
    next();  // consume '{'
    while (tk != '}') stmt();
    next();  // consume '}'
  }
  else if (tk == ';') {
    next();  // empty statement: just consume the semicolon
  }
  else {
    expr(Assign);  // parse an expression statement
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
}
This is the entry point of the compiler. It performs the following:
// Processes command-line arguments to set flags
// Opens and reads the source file into memory
// Allocates memory for the symbol table, emitted code, data area, and stack
// Initializes the symbol table with keywords and system/library functions
// Parses global declarations, including functions and variables
// Sets up the stack and then runs the compiled code using a simple virtual machine
int main(int argc, char **argv)
{
  int fd, bt, ty, poolsz, *idmain;
  int *pc, *sp, *bp, a, cycle;  // Virtual machine registers: program counter, stack pointer, base pointer, etc.
  int i, *t;  // Temporary variables

  --argc; ++argv;
  if (argc > 0 && **argv == '-' && (*argv)[1] == 's') { src = 1;  // Enable source and assembly output
    --argc; ++argv; }
  if (argc > 0 && **argv == '-' && (*argv)[1] == 'd') { debug = 1;  // Enable debug mode (prints executed instructions)
     --argc; ++argv; }
  if (argc < 1) { printf("usage: c4 [-s] [-d] file ...\n"); return -1; }
  // Open the source file.
  if ((fd = open(*argv, 0)) < 0) { printf("could not open(%s)\n", *argv); return -1; }

  poolsz = 256*1024;  // Define an arbitrary memory pool size for symbol, code, data, and stack areas.
  // Allocate the symbol table.
  if (!(sym = malloc(poolsz))) { printf("could not malloc(%d) symbol area\n", poolsz); return -1; }
  // Allocate the text area (emitted code).
  if (!(le = e = malloc(poolsz))) { printf("could not malloc(%d) text area\n", poolsz); return -1; }
  // Allocate the data area.
  if (!(data = malloc(poolsz))) { printf("could not malloc(%d) data area\n", poolsz); return -1; }
  // Allocate the stack area.
  if (!(sp = malloc(poolsz))) { printf("could not malloc(%d) stack area\n", poolsz); return -1; }
  // Initialize the allocated areas to zero.
  memset(sym,  0, poolsz);
  memset(e,    0, poolsz);
  memset(data, 0, poolsz);
  // Initialize the symbol table with C keywords.
  p = "char else enum if int return sizeof while "
      "open read close printf malloc free memset memcmp exit void main";
  i = Char; while (i <= While) { next();id[Tk] = i++;  // Associate each keyword with its corresponding token value.
 } // add keywords to symbol table
// Add library/system function names to the symbol table.
  i = OPEN; while (i <= EXIT) {
    next(); 
    id[Class] = Sys;  // Mark as a system function.
    id[Type] = INT;   // Assume system functions return int.
    id[Val] = i++;    // Store the system call number.
                              } // add library to symbol table
  next(); 
  id[Tk] = Char;  // Handle the 'void' type as if it were a char.
  next(); 
  idmain = id;  // Save the identifier for 'main' for later use.

   // Allocate memory for the source code and read the file.
  if (!(lp = p = malloc(poolsz))) { 
    printf("could not malloc(%d) source area\n", poolsz); 
    return -1;
  }
  if ((i = read(fd, p, poolsz-1)) <= 0) { 
    printf("read() returned %d\n", i); 
    return -1;
  }
  p[i] = 0;  // Null-terminate the source code.
  close(fd);

  // Start parsing global declarations.
  line = 1;
  next();  // Get the first token.
  while (tk) {
    bt = INT;  // Default base type is int.
    if (tk == Int) next();
    else if (tk == Char) { next(); bt = CHAR; }
    else if (tk == Enum) {
      next();
      if (tk != '{') next();
      if (tk == '{') {
        next();
        i = 0;
        // Parse enum definitions.
        while (tk != '}') {
          if (tk != Id) { printf("%d: bad enum identifier %d\n", line, tk); return -1; }
          next();
          if (tk == Assign) {
            next();
            if (tk != Num) { printf("%d: bad enum initializer\n", line); return -1; }
            i = ival;
            next();
          }
      // Add the enum constant to the symbol table.
          id[Class] = Num; id[Type] = INT; id[Val] = i++;
          if (tk == ',') next();
        }
        next();
      }
    }
// Handle multiple declarations (variables or functions) separated by commas.
    while (tk != ';' && tk != '}') {
      ty = bt;
      while (tk == Mul) { next(); ty = ty + PTR; }  // Process pointer declarations.
      if (tk != Id) { printf("%d: bad global declaration\n", line); return -1; }
      if (id[Class]) { printf("%d: duplicate global definition\n", line); return -1; }
      next();
      id[Type] = ty;
      if (tk == '(') { // function definition
        id[Class] = Fun;
        id[Val] = (int)(e + 1);  // Save the function's entry address in the emitted code.
        next(); i = 0;
    // Parse the function parameters.
        while (tk != ')') {
          ty = INT;
          if (tk == Int) next();
          else if (tk == Char) { next(); ty = CHAR; }
          while (tk == Mul) { next(); ty = ty + PTR; }
          if (tk != Id) { printf("%d: bad parameter declaration\n", line); return -1; }
          if (id[Class] == Loc) { printf("%d: duplicate parameter definition\n", line); return -1; }
          id[HClass] = id[Class]; id[Class] = Loc;
          id[HType]  = id[Type];  id[Type] = ty;
          id[HVal]   = id[Val];   id[Val] = i++;
          next();
          if (tk == ',') next();
        }
        next();
        if (tk != '{') { printf("%d: bad function definition\n", line); return -1; }
        loc = ++i;  // Initialize local variable offset.
        next();  // Consume '{'
        // Parse local variable declarations inside the function.
        while (tk == Int || tk == Char) {
          bt = (tk == Int) ? INT : CHAR;
          next();
          while (tk != ';') {
            ty = bt;
            while (tk == Mul) { next(); ty = ty + PTR; }
            if (tk != Id) { printf("%d: bad local declaration\n", line); return -1; }
            if (id[Class] == Loc) { printf("%d: duplicate local definition\n", line); return -1; }
            // Save previous local variable info and update the symbol table.
            id[HClass] = id[Class]; id[Class] = Loc;
            id[HType]  = id[Type];  id[Type] = ty;
            id[HVal]   = id[Val];   id[Val] = ++i;
            next();
            if (tk == ',') next();
          }
          next();  // Consume semicolon after local declarations.
        }
        *++e = ENT; *++e = i - loc;  // Emit entry instruction with space for local variables.
        while (tk != '}') stmt();  // Parse statements inside the function.
        *++e = LEV;  // Emit leave instruction to return from the function.
        // Unwind the symbol table to remove local variable definitions.
        id = sym;
        while (id[Tk]) {
          if (id[Class] == Loc) {
            id[Class] = id[HClass];
            id[Type] = id[HType];
            id[Val] = id[HVal];
          }
          id = id + Idsz;
        }
      }
      else {  // Global variable declaration.
        id[Class] = Glo;
        id[Val] = (int)data;  // Assign an address in the data area.
        data = data + sizeof(int);  // Advance the data pointer
      }
      if (tk == ',') next();
    }
    next();  // Consume the semicolon or closing brace.
  }
  // Ensure that the main() function is defined.
  if (!(pc = (int *)idmain[Val])) { printf("main() not defined\n"); return -1; }
  if (src) return 0;  // If source output is enabled, do not execute the compiled code.

  // Set up the stack for the virtual machine.
  bp = sp = (int *)((int)sp + poolsz);
  *--sp = EXIT;  // Push the exit instruction (called if main returns).
  *--sp = PSH; t = sp;
  *--sp = argc;      // Push argument count.
  *--sp = (int)argv; // Push pointer to arguments.
  *--sp = (int)t;    // Push pointer to saved state.


  // Start the virtual machine loop to execute the compiled code.
  cycle = 0;
  while (1) {
    i = *pc++;  // Fetch the next opcode.
    ++cycle;
    if (debug) { // If debug mode is on, print the executed instruction along with its mnemonic.
      printf("%d> %.4s", cycle,
        &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
         "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
         "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[i * 5]);
      if (i <= ADJ) printf(" %d\n", *pc); else printf("\n");
    }
// Execute instructions based on their opcode.
    if      (i == LEA) a = (int)(bp + *pc++);  // Load the address of a local variable.
    else if (i == IMM) a = *pc++;              // Load an immediate value.
    else if (i == JMP) pc = (int *)*pc;          // Unconditional jump.
    else if (i == JSR) { *--sp = (int)(pc + 1); pc = (int *)*pc; }  // Jump to subroutine.
    else if (i == BZ)  pc = a ? pc + 1 : (int *)*pc;  // Branch if zero.
    else if (i == BNZ) pc = a ? (int *)*pc : pc + 1;  // Branch if not zero.
    else if (i == ENT) { *--sp = (int)bp; bp = sp; sp = sp - *pc++; }  // Enter subroutine: setup new stack frame.
    else if (i == ADJ) sp = sp + *pc++;         // Adjust the stack pointer.
    else if (i == LEV) { sp = bp; bp = (int *)*sp++; pc = (int *)*sp++; }  // Leave subroutine: restore previous frame.
    else if (i == LI)  a = *(int *)a;            // Load an int from memory.
    else if (i == LC)  a = *(char *)a;           // Load a char from memory.
    else if (i == SI)  *(int *)*sp++ = a;         // Store an int.
    else if (i == SC)  a = *(char *)*sp++ = a;      // Store a char.
    else if (i == PSH) *--sp = a;                 // Push a value onto the stack.                                   // push

    else if (i == OR)  a = *sp++ |  a;   // Bitwise OR: combine top of stack with a
    else if (i == XOR) a = *sp++ ^  a;   // Bitwise XOR: combine top of stack with a
    else if (i == AND) a = *sp++ &  a;   // Bitwise AND: combine top of stack with a
    else if (i == EQ)  a = *sp++ == a;    // Equality: check if top of stack equals a
    else if (i == NE)  a = *sp++ != a;    // Inequality: check if top of stack not equals a
    else if (i == LT)  a = *sp++ <  a;    // Less-than: compare top of stack with a
    else if (i == GT)  a = *sp++ >  a;    // Greater-than: compare top of stack with a
    else if (i == LE)  a = *sp++ <= a;    // Less-or-equal: compare top of stack with a
    else if (i == GE)  a = *sp++ >= a;    // Greater-or-equal: compare top of stack with a
    else if (i == SHL) a = *sp++ << a;    // Left shift: shift top of stack left by a
    else if (i == SHR) a = *sp++ >> a;    // Right shift: shift top of stack right by a
    else if (i == ADD) a = *sp++ +  a;    // Addition: add top of stack to a
    else if (i == SUB) a = *sp++ -  a;    // Subtraction: subtract a from top of stack
    else if (i == MUL) a = *sp++ *  a;    // Multiplication: multiply top of stack by a
    else if (i == DIV) a = *sp++ /  a;    // Division: divide top of stack by a
    else if (i == MOD) a = *sp++ %  a;    // Modulus: remainder of dividing top of stack by a
        
// Handle system calls.
    else if (i == OPEN) a = open((char *)sp[1], *sp);      // Open file: filename at sp[1], flags in *sp
    else if (i == READ) a = read(sp[2], (char *)sp[1], *sp); // Read: file descriptor at sp[2], buffer at sp[1], size *sp
    else if (i == CLOS) a = close(*sp);                      // Close file: file descriptor in *sp
    else if (i == PRTF) {                                   // Print formatted output using stack arguments
      t = sp + pc[1];                                      // t points to arguments for printf
      a = printf((char *)t[-1], t[-2], t[-3], t[-4], t[-5], t[-6]);
    }
    else if (i == MALC) a = (int)malloc(*sp);               // Allocate memory of size *sp
    else if (i == FREE) free((void *)*sp);                  // Free memory at address *sp
    else if (i == MSET) a = (int)memset((char *)sp[2], sp[1], *sp); // Set *sp bytes at sp[2] to value sp[1]
    else if (i == MCMP) a = memcmp((char *)sp[2], (char *)sp[1], *sp); // Compare *sp bytes at sp[2] and sp[1]
    else if (i == EXIT) {                                  // Exit program with code in *sp
      printf("exit(%d) cycle = %d\n", *sp, cycle);
      return *sp;
    }
    else {                                                 // Unknown instruction: error out
      printf("unknown instruction = %d! cycle = %d\n", i, cycle);
      return -1;
    }
  }
}
