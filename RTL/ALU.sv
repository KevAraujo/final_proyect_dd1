module ALU #(parameter WIDTH = 4) (
  input wire [WIDTH-1:0] a, b,
  input wire [2:0] select,
  input wire arst,
  output wire [WIDTH*2-1:0] out,
  output wire a_greater, a_equal, a_less,inf,
  input wire clk,
  input wire enable,
  output wire carry_out
);
  

  selection #(WIDTH) u_selection (
    .a(a),
    .b(b),
    .select(select),
    .enable(enable),
    .arst(arst),
    .out(out),
    .carry_out(carry_out), 
    .a_greater(a_greater),
    .a_equal(a_equal),
    .a_less(a_less),
    .inf,
    .clk(clk)
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
  output reg [WIDTH:0] diff,
  output reg sign,
  input wire clk
);

wire [WIDTH-1:0] signed_b;
//reg sign;
assign signed_b = ~b+1;

always @(a or b) if (b > a) begin
sign = 1;
diff = ~(a + signed_b-1);
end

else begin
sign = 0;
diff = {(a + signed_b)};
end

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
  output wire [WIDTH-1:0] div,
  output wire inf
);

  assign div = a / b;
  assign inf = (b == 0)? 1'b1 : 1'b0;
  
endmodule

//Selección
module selection #(parameter WIDTH = 4)(
  input wire [WIDTH-1:0] a, b,
  input wire [2:0] select,
  output reg [WIDTH*2-1:0] out,
  wire [WIDTH-1:0] result_add, result_sub,div,
  wire [WIDTH-1:0] r_and, r_or, r_xor,
  wire [WIDTH*2-1:0] result_mul,
  output wire a_greater, a_equal, a_less,
  wire inst_inf,
  output reg inf,
  output reg carry_out,
  input wire enable,
  input wire arst,
  input wire clk
);
  int carry;
  multiplicator #(WIDTH) u_multiplicator (
    .a(a),
    .b(b),
    .multiplication(result_mul)
  );
  divisor #(WIDTH) u_divisor (
    .a(a),
    .b(b),
    .div(div),
    .inf(inst_inf)
  );
  
    adder #(WIDTH) u_adder (
      .a(a),
      .b(b),
      .sum(result_add),
      .carry_out(carry)
  );

  subtractor #(WIDTH) u_subtractor (
	  .a(a),
	  .b(b),
	  .diff(result_sub)
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
  
  always @(posedge clk or posedge arst) begin
  inf = inst_inf;
  if (arst == 0)begin
    if (enable == 1)begin
        out = (select == 3'b000) ? (result_add) : (select == 3'b001) ? result_sub : (select == 3'b010) ? r_and : (select == 3'b011) ? r_or : (select == 3'b100) ? r_xor : (select == 3'b101) ? a_equal : (select == 3'b110) ? result_mul : (select == 3'b111) ? div : 0;
        carry_out = (select == 3'b000) ? carry : 0;
        end
    else begin
        out = '0;
        carry_out = 0;
        end
  end
  else
  out = 0;
  end
endmodule
