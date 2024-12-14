module ALU_VECTORIAL #(parameter WIDTH = 8, n_alu = 4)(
    input logic clk,               // Reloj de entrada
    //input logic rst,           // Señal de reset
    input wire [WIDTH*n_alu-1:0] a,    // Entrada de datos
    input wire [WIDTH*n_alu-1:0] b,
    input wire [2:0] select,
    input wire arst,
    //input wire enable,
    output wire [n_alu-1:0]carry_out,
    input wire [n_alu-1:0] enable,
    output wire [n_alu-1:0] a_greater, a_equal, a_less, inf,
    output wire [WIDTH*n_alu*2-1:0] data_out   // Salida de datos
);
//logic [WIDTH*n_alu-1:0]a_w;
//assign a = a_w + 16'h0100;
    // Declaración de la cantidad de instancias
    genvar i;

    // Generación de instancias del módulo `mi_modulo`
    generate
        for (i = 0; i < n_alu; i = i + 1) begin : gen_inst
            ALU u_modulo (
                .clk(clk),
                //.rst(rst),
                .a(a[(i*WIDTH) +: WIDTH]),
                .b(b[(i*WIDTH) +: WIDTH]),
                .out(data_out[i*WIDTH*2 +: (WIDTH*2)]),
                .select(select),
                .arst(arst),
                .enable(enable[i]),
                .carry_out(carry_out[i]), 
                .a_greater(a_greater[i]),
                .a_equal(a_equal[i]),
                .a_less(a_less[i]),
                .inf(inf[i])
            );
        end
    endgenerate

endmodule
