`timescale 1ns/1ps

module alu_tb;

    parameter WIDTH = 8;
    parameter n_alu = 4;
    parameter GLOBAL_TIMEOUT = 1000000;

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
    /*
    always @(posedge clk)
    for (i = 0; i < (WIDTH * n_alu); i = i + WIDTH);
    
    
    property check_sum;
    @(posedge clk) (alu_vif.select == '0) |-> (alu_vif.out[2*i-1+:i*2] == $past(alu_vif.a[i-1+:i]) + $past(alu_vif.b[i-1+:i]));
   endproperty
    assert property (check_sum) else $error("ADDER has not donne the sum correctly.");
*/
    always #10 clk = ~clk;
    
    //`define test_all_random;
    `define test_suma;
    //`define test_resta;
    
    logic tmp_a;
    logic tmp_b;
    always @(posedge clk) begin
         tmp_a = alu_vif.a;
         tmp_b = alu_vif.b;
         @(posedge clk);
         $display("A = %0d;  B = %0d;  carry out = %0d;   out = %0d", tmp_a, tmp_b, alu_vif.carry_out, alu_vif.out);
    end

    // Main test
    initial begin
        //$dumpfile("dump.vcd");
        //$dumpvars;

        $display("WELCOME!");

        clk = 0;
        

    end

    initial begin
        #GLOBAL_TIMEOUT;
        $display("EOT");
        $finish;
    end


`ifdef test_all_random

    initial begin
    alu_vif.test_sel_random();
    $finish;
    end           
            
`endif

`ifdef test_suma

    initial begin
    alu_vif.sel_value(3'b000);
    //alu_vif.test_reset_random();
    alu_vif.test_full_random();
    alu_vif.test_a_greater_than_b();
    alu_vif.test_b_greater_than_a();
    end
 
`endif

`ifdef test_resta

    initial begin
    alu_vif.sel_value(3'b001);
    //alu_vif.test_reset_random();
    alu_vif.test_full_random();
    alu_vif.test_a_greater_than_b();
    alu_vif.test_b_greater_than_a();
    end
 
`endif

`ifdef test_multiplicación

    initial begin
    alu_vif.sel_value(3'b111);
    //alu_vif.test_reset_random();
    alu_vif.test_full_random();
    alu_vif.test_a_greater_than_b();
    alu_vif.test_b_greater_than_a();
    end
 
`endif

endmodule
