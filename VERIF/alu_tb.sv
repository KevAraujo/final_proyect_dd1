`timescale 1ns/1ps

module alu_tb;

    parameter WIDTH = 4;
    parameter n_alu = 4;
    parameter GLOBAL_TIMEOUT = 100000;
    parameter GLOBAL_TIMEOUT_ON = 0;

    logic clk;

    alu_if #(WIDTH, n_alu) alu_vif(clk);

    ALU_VECTORIAL #(.WIDTH(WIDTH), .n_alu(n_alu)) DUT (
        .clk(alu_vif.clk), 
        .arst(alu_vif.arst),          
        .a(alu_vif.a),  
        .b(alu_vif.b),
        .select(alu_vif.select),
        .enable(alu_vif.enable),
        .carry_out(alu_vif.carry_out),
        .a_greater(alu_vif.a_greater), .a_equal(alu_vif.a_equal), .a_less(alu_vif.a_less), .inf(alu_vif.inf),
        .data_out(alu_vif.out)
    );
    
    function eot();
        $display("EOT");
        $display("Overall coverage: %.2f%%", $get_coverage());
        $finish;
    endfunction

    always #5 clk = ~clk;

    // Main test
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;

        $display("WELCOME!");
        alu_vif.hello_world();

        clk = 0;
        alu_vif.test_0_random();
        alu_vif.test_n_random(10);
        alu_vif.test_sel_random();

        eot();
        $finish;
    end

    initial begin
        if (GLOBAL_TIMEOUT_ON) begin
            #GLOBAL_TIMEOUT;
            eot();
            $finish;
        end
    end

endmodule
