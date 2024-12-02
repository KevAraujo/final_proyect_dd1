module ALU_VECTORIAL #(parameter WIDTH = 4, n_alu = 4)(
    input logic clk,               // Reloj de entrada
    input wire [WIDTH*n_alu:0] a,    // Entrada de datos
    input wire [WIDTH*n_alu:0] b,
    input wire [2:0] select,
    input wire arst,
    output wire carry_out,
    output wire [WIDTH:0]enable,
    output wire a_greater, a_equal, a_less,
    output wire [WIDTH*n_alu*8-1:0] data_out   // Salida de datos
);

    // Declaración de la cantidad de instancias
    genvar i;

    // Generación de instancias del módulo `mi_modulo`
    generate
        for (i = 0; i < n_alu; i = i + 1) begin : gen_inst
            ALU u_modulo (
                .clk(clk),
                .a(a[(i*WIDTH) +: WIDTH]),
                .b(b[(i*WIDTH) +: WIDTH]),
                .out(data_out[i*8 +: 8]),
                .select(select),
                .arst(arst),
                .enable(enable[i]),
                .carry_out(carry_out), 
                .a_greater(a_greater),
                .a_equal(a_equal),
                .a_less(a_less)
            );
        end
    endgenerate

endmodule
