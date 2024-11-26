module alu_tb;

    parameter WIDTH = 4;
    parameter n_alu = 4;
    parameter GLOBAL_TIMEOUT = 100;

    logic clk;
    //logic rst;
    logic [WIDTH*n_alu:0] a;
    logic [WIDTH*n_alu:0] b;
    logic [2:0] select;
    logic carry_out;
    logic a_greater, a_equal, a_less;
    logic [WIDTH*n_alu*8-1:0] data_out;

    ALU_VECTORIAL #(.WIDTH(WIDTH), .n_alu(n_alu)) DUT (
        .clk(clk), 
        //.rst(rst),          
        .a(a),  
        .b(b),
        .select(select),
        .carry_out(carry_out),
        .a_greater(a_greater), .a_equal(a_equal), .a_less(a_less),
        .data_out(data_out)
    );

    initial begin
        $display("WELCOME!");
    end

    initial begin
        #GLOBAL_TIMEOUT;
        $display("EOT");
        $finish;
    end

endmodule