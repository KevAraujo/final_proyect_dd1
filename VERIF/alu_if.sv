interface alu_if #(parameter WIDTH = 4, n_alu = 4)(input clk);
  logic [WIDTH*n_alu-1:0] a;
  logic [WIDTH*n_alu-1:0] b;
  logic [2:0] select;
  logic a_greater, a_equal, a_less;
  logic [WIDTH*n_alu*8-1:0] out;
  logic [0:0] carry_out;
  
endinterface
