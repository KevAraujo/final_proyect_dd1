module ALU #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  input wire [2:0] select,
  output wire [WIDTH*2-1:0] out,
  output wire [WIDTH-1:0] result_add, result_sub,div,
  output wire [WIDTH-1:0] r_and, r_or, r_xor,
  output wire [WIDTH*2-1:0] result_mul,
  output wire a_greater, a_equal, a_less,
  output wire carry_out
);
  

  selection #(WIDTH) u_selection (
    .a(a),
    .b(b),
    .select(select),
    .out(out),
    .result_add(result_add),
    .carry_out(carry_out),
    .result_sub(result_sub),
    .r_and(r_and),
    .r_or(r_or),
    .r_xor(r_xor),
    .a_greater(a_greater),
    .a_equal(a_equal),
    .a_less(a_less),
    .result_mul(result_mul),
    .div(div)
  );

 
endmodule

//suma___________________________________________________________
module adder #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH-1:0] sum,
  output wire [0:0] carry_out          // Acarreo de salida
);

  assign {carry_out, sum} = a + b;  // Suma con acarreo
endmodule
//Resta__________________________________________________________
module subtractor #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH-1:0] diff

);
        // Usamos un ancho mayor para manejar el borrow

  assign diff = a - b; // Agregamos un bit extra para manejar el borrow
 // El bit más significativo de 'result' es el borrow

endmodule

//Bitwise and____________________________________________________
module bitwise_and #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH-1:0] bitwiseand
);
   assign bitwiseand = a & b;       //bitwise AND
   
endmodule

//Bitwise or_____________________________________________________
module bitwise_or #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH-1:0] bitwiseor
);
  assign bitwiseor = a | b;        //bitwise OR
  
endmodule

//Bitwise xor____________________________________________________
module bitwise_xor #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH-1:0] bitwisexor
);
assign bitwisexor = a ^ b;       //bitwise exclusive-OR 
  
endmodule

//Comparador_____________________________________________________
module comparator #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire a_greater, a_equal, a_less
);

  assign a_greater = (a > b);
  assign a_equal = (a == b);
  assign a_less = (a < b);
endmodule

//Multiplicator
module multiplicator #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH*2-1:0] multiplication
);

  assign multiplication = a * b;
endmodule

//Divisor
module divisor #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  output wire [WIDTH-1:0] div
);

  assign div = a / b;
endmodule

//Selección
module selection #(parameter WIDTH = 4)(
  input wire [WIDTH-1:0] a, b,
  input wire [2:0] select,
  output wire [WIDTH*2-1:0] out,
  output wire [WIDTH-1:0] result_add, result_sub,div,
  output wire [WIDTH-1:0] r_and, r_or, r_xor,
  output wire [WIDTH*2-1:0] result_mul,
  output wire a_greater, a_equal, a_less,
  output wire carry_out 
);
  
  multiplicator #(WIDTH) u_multiplicator (
    .a(a),
    .b(b),
    .multiplication(result_mul)
  );
  divisor #(WIDTH) u_divisor (
    .a(a),
    .b(b),
    .div(div)
  );
  
    adder #(WIDTH) u_adder (
      .a(a),
      .b(b),
      .sum(result_add),
      .carry_out(carry_out)
  );

  subtractor #(WIDTH) u_subtractor (
	a, b, result_sub
  );

  comparator #(WIDTH) u_comparator (
    .a(a),
    .b(b),
    .a_greater(a_greater),
    .a_equal(a_equal),
    .a_less(a_less)
  );

  bitwise_and #(WIDTH) u_bitwise_and (
    .a(a),
    .b(b),
    .bitwiseand(r_and)
  );
  
  bitwise_or #(WIDTH) u_bitwise_or (
    .a(a),
    .b(b),
    .bitwiseor(r_or)
  );
  
  bitwise_xor #(WIDTH) u_bitwise_xor(
    .a(a),
    .b(b),
    .bitwisexor(r_xor)
  );
  assign out = (select == 3'b000) ? {carry_out, result_add} : (select == 3'b001) ? result_sub : (select == 3'b010) ? r_and : (select == 3'b011) ? r_or : (select == 3'b100) ? r_xor : (select == 3'b101) ? a_equal : (select == 3'b110) ? result_mul : (select == 3'b111) ? div : 0;
endmodule
