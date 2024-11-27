`timescale 1ns/1ps

module alu_tb;

    parameter WIDTH = 4;
    parameter n_alu = 4;
    parameter GLOBAL_TIMEOUT = 100;

    logic clk;

    alu_if #(WIDTH, n_alu) alu_vif(clk);

    ALU_VECTORIAL #(.WIDTH(WIDTH), .n_alu(n_alu)) DUT (
        .clk(alu_vif.clk), 
        //.rst(alu_vif.rst),          
        .a(alu_vif.a),  
        .b(alu_vif.b),
        .select(alu_vif.select),
        .carry_out(alu_vif.carry_out),
        .a_greater(alu_vif.a_greater), .a_equal(alu_vif.a_equal), .a_less(alu_vif.a_less),
        .data_out(alu_vif.out)
    );

    always #5 clk = ~clk;

    initial begin
        clk = 0;
    end

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

    initial begin
        $display("WELCOME!");
        alu_vif.hello_world();
    end

    initial begin
        #GLOBAL_TIMEOUT;
        $display("EOT");
        $finish;
    end

endmodule