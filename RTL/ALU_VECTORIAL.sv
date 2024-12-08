module ALU_VECTORIAL #(parameter WIDTH = 4, n_alu = 1)(
    input logic clk,               // Reloj de entrada
    //input logic rst,           // Señal de reset
    input wire [WIDTH*n_alu-1:0] a,    // Entrada de datos
    input wire [WIDTH*n_alu-1:0] b,
    input wire [2:0] select,
    input wire arst,
    //input wire enable,
    output wire carry_out,
    input wire [n_alu-1:0] enable,
    output wire a_greater, a_equal, a_less, inf,
    output wire [WIDTH*n_alu*2-1:0] data_out   // Salida de datos
);

    genvar i;

    generate
        for (i = 0; i < n_alu; i = i + 1) begin : gen_inst
            ALU u_modulo (
                .clk(clk),
                //.rst(rst),
                .a(a[(i*WIDTH) +: WIDTH]),
                .b(b[(i*WIDTH) +: WIDTH]),
                .out(data_out[i*8 +: 8]),
                .select(select),
                .arst(arst),
                .enable(enable[i]),
                .carry_out(carry_out), 
                .a_greater(a_greater),
                .a_equal(a_equal),
                .a_less(a_less),
                .inf(inf[i])
            );
        end
