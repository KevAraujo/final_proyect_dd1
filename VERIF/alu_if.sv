interface alu_if #(parameter WIDTH = 4, n_alu = 1)(input clk);
  logic [WIDTH*n_alu-1:0] a;
  logic [WIDTH*n_alu-1:0] b;
  logic [2:0] select;
  logic a_greater, a_equal, a_less, inf;
  logic [WIDTH*n_alu*2-1:0] out;
  logic [0:0] carry_out;
  logic [n_alu-1:0] enable;
  logic arst;

  initial begin
  select = 3'b000;
  a = 0;
  b = 0;
  enable = '1;
  arst = 0;
  end
  // BFM for stimuli
  function automatic hello_world();
    $display("Hello world from [%m]!");
  endfunction

  function automatic reset(input integer value);
    reset = value;
  endfunction

  function automatic reset_random();
    std::randomize(arst);
  endfunction

  function automatic a_random();
    std::randomize(a);
  endfunction

  function automatic a_greater_b_random();
    if (!std::randomize(a, b) with {a > b;} ) begin
      $display("Randomization in [%m] failed!");
    end
  endfunction

  function automatic b_random();
    std::randomize(b);
  endfunction

  function automatic b_greater_a_random();
    if (!std::randomize(a, b) with {b > a;} ) begin
      $display("Randomization in [%m] failed!");
    end
  endfunction

  function automatic sel_random();
    std::randomize(select);
  endfunction

  function automatic sel_value(input integer value);
    select = value;
  endfunction

  function automatic a_value(input integer value);
    a = value;
  endfunction

  function automatic b_value(input integer value);
    b = value;
  endfunction

  function automatic a_random_b_zero();
    if (!std::randomize(a)) begin
      $display("Randomization of 'a' in [%m] failed!");
    end
    b = 0;
  endfunction

  function automatic b_random_a_zero();
    if (!std::randomize(b)) begin
      $display("Randomization of 'b' in [%m] failed!");
    end
    a = 0;
  endfunction

  function automatic a_max_b_random();
    a = '1; 
    if (!std::randomize(b)) begin
      $display("Randomization of 'b' in %m failed!");
    end
  endfunction


  function automatic b_max_a_random();
    b = '1; 
    if (!std::randomize(a)) begin
      $display("Randomization of 'a' in %m failed!");
    end
  endfunction

  function automatic a_near_max_min_b_random(input integer value);
    std::randomize(a) with{ (a > (WIDTH * WIDTH) - (value)) || (a < (value));};
  std::randomize(b);
  endfunction
  
  function automatic b_near_max_min_a_random(input integer value);
    std::randomize(b) with{ (b > (WIDTH * WIDTH) - (value)) || (b < (value));};
  std::randomize(a);
  endfunction
  
  function automatic a_b_random_overflow();
  std::randomize(a, b) with{b + a == WIDTH*WIDTH;};
  endfunction
  
  
  //------------------------------- BFM for testing--------------------------------------------
  int cnt;
  
  task automatic test_carry_random();
    repeat (50)@(posedge clk)begin
    a_b_random_overflow();
    end
  endtask
  
  task automatic test_max_mid_min_value();
  event event_a;
  event event_b;
    @(posedge clk)begin
    a_value('1);
    b_value('1);
    ->event_a;
    end
    
    wait(event_a.triggered);
    @(posedge clk)begin
    a_value(WIDTH*WIDTH/2);
    b_value(WIDTH*WIDTH/2);
    ->event_b;
    end
    
    wait(event_b.triggered);
    @(posedge clk)begin
    a_value('0);
    b_value('0);
    end
    
  endtask
  
  task automatic test_0_random();
    int i; 
    for (i = 0; i < 50; i = i + 1) begin
      b_random_a_zero(); 
      $display("Iteration %0d: b_random_a_zero: a = %0d, b = %0d", i, a, b); 
      @(posedge clk);
    end
    for (i = 0; i < 50; i = i + 1) begin
      a_random_b_zero(); 
      $display("Iteration %0d: a_random_b_zero: a = %0d, b = %0d", i, a, b); 
      @(posedge clk);
    end
  endtask
  
  task automatic test_directed_test(input integer value1, value2);
    a_value(value1);
    b_value(value2);
  endtask
  
  task automatic test_full_random();
    repeat (100)@(posedge clk)begin
    a_random();
    b_random();
    end
  endtask
  
  task automatic test_a_greater_than_b();
    repeat (100)@(posedge clk)begin
    a_greater_b_random();
    end
  endtask
  
  task automatic test_b_greater_than_a();
    repeat (100)@(posedge clk)begin
    b_greater_a_random();
    end
  endtask
  
  task automatic test_reset_random();
    fork
      // Bloque 1: Randomizar `a` y `b` en el próximo flanco de reloj
      repeat (100)@(posedge clk) begin
        a=$random;
        b=$random;
      end

      repeat (100) begin
        arst=$random;
        #15;
      end
      join
  endtask
  
  task automatic test_reset_timed(input integer value);
    fork
      // Bloque 1: Randomizar `a` y `b` en el próximo flanco de reloj
      repeat (50)@(posedge clk) begin
        a=$random;
        b=$random;
      end

        arst=$random;
        #25;
      join
  endtask
  
  task automatic test_sel_random();
    fork
      // Bloque 1: Randomizar `a` y `b` en el próximo flanco de reloj
      repeat (400)@(posedge clk) begin
        a=$random;
        b=$random;
      end

      repeat (400) begin
        sel_random();
      end
      join
  endtask

  task automatic test_n_random(int n);
    enable = 1;
    cnt = 0;
    repeat(n) begin
      a_random();
      b_random();
      sel_random();
      $display("[%m] iteration=%0d select=%0d, a=%0d, b=%0d", cnt, select, a, b);
      @(posedge clk)
      cnt++;
    end
    enable = 0;
  endtask


  task automatic test_all_possible_combinations();
    enable = 1;
    cnt = 0;
    for(int i = 0; i < 2**$bits(select); i++) for(int y = 0; y < 2**$bits(a); y++) for(int z = 0; z < 2**$bits(b); z++) begin
      $display("Iteration[%0d]: select=%0d, a=%0d, b=%0d", cnt, i, y, z);
      select = i;
      a = y;
      b = z;
      cnt++;
      @(posedge clk);
    end
  endtask


  //-------------------------------------------- Coverage ------------------------------------------------
  
  covergroup alu_covergroup @(posedge clk);

    cg_select_all_values: coverpoint select {
      bins select_000 = {3'b000};
      bins select_001 = {3'b001};
      bins select_010 = {3'b010};
      bins select_011 = {3'b011};
      bins select_100 = {3'b100};
      bins select_101 = {3'b101};
      bins select_110 = {3'b110};
      bins select_111 = {3'b111};
    }

    cg_A_all_values: coverpoint a;
    cg_B_all_values: coverpoint b;
    cg_A_max_value: coverpoint a {
      bins max_value = {'1};
    }
    cg_A_min_value: coverpoint a {
      bins min_value = {'0};
    }
    cg_B_max_value: coverpoint b {
      bins max_value = {'1};
    }
    cg_B_min_value: coverpoint b {
      bins min_value = {'0};
    }

    cg_enable_all_values: coverpoint enable {
      bins enabled = {1'b1};
      bins disabled = {1'b0};
    }

    cg_cross_enable_sel: cross select, enable;

    cg_carry_out_all_values: coverpoint carry_out {
      bins carry_zero = {1'b0};
      bins carry_one = {1'b1};
    }

    cross select, carry_out;
  endgroup

  covergroup transition_cg @(posedge clk);
    coverpoint enable {
      bins enable_rise = (0 => 1); 
      bins enable_fall = (1 => 0); 
    }
    coverpoint arst {
      bins arst_rise = (0 => 1); 
      bins arst_fall = (1 => 0); 
    }
    coverpoint clk {
      bins clk_rise = (0 => 1); 
      bins clk_fall = (1 => 0); 
    }
    
    // Toggle coverage of all bits in A and B

  endgroup

  alu_covergroup alu_cg;
  transition_cg trans_cg;

  initial begin
    alu_cg = new();
    forever @(posedge clk) begin
      alu_cg.sample();
    end
  end
  
  
  //------------------------------------------- Assertions -----------------------------------------------
  
     logic [WIDTH-1:0] past_a;
  logic [WIDTH-1:0] past_b;
   always @(posedge clk) begin
   past_a=$past(a[WIDTH-1:0]);
   past_b=$past(b[WIDTH-1:0]);
   end
   /*
   genvar i;
   for(i=0;i<4;i = i+1) begin:check_add_loop
   property check_sum;
    @(posedge clk) (select == '0) |-> (out[WIDTH*2*(i+1)-1:WIDTH*2*i] == (past_a[WIDTH*(i+1)-1:WIDTH*i] + past_b[WIDTH*(i+1)-1:WIDTH*i]));//$past(a[WIDTH*(i+1)-1:WIDTH*i]) + $past(b[WIDTH*(i+1)-1:WIDTH*i]));
   endproperty
   assert property (check_add_loop[i].check_sum) else $error("ADDER[%0d] has not donne the sum correctly out -> %0h, a -> %0h, b -> %0h, sum -> %0h.",i, {carry_out[i],out[(WIDTH*2*(i)+WIDTH-1):WIDTH*2*i]},past_a[WIDTH*(i+1)-1:WIDTH*i], past_b[WIDTH*(i+1)-1:WIDTH*i],(past_a[WIDTH*(i+1)-1:WIDTH*i] + past_b[WIDTH*(i+1)-1:WIDTH*i]));
   end
   */
   /*
   property check_sum;
    @(posedge clk) (select == '0) |-> (out[WIDTH*2-1:0] <= past_a + past_b);
   endproperty
   assert property (check_sum) else $error("ADDER has not donne the sum correctly out -> %0d, a -> %0d b -> %0d.", (out[WIDTH*2-1:0]),past_a, past_b);
    */
   property check_carry_out_1;
    @(posedge clk)((select == '0) && ((b[WIDTH-1:0] + a[WIDTH-1:0]) > WIDTH*WIDTH-1)) |=> (carry_out[0:0] > 0);
   endproperty
   assert property (check_carry_out_1) else $error("carry_out should have a high value.");

   property check_carry_out_0;
    @(posedge clk)((select == '0) && (a[WIDTH-1:0] + b[WIDTH-1:0] <= WIDTH*WIDTH-1)) |=> (carry_out[0:0] == 0);
   endproperty
   assert property (check_carry_out_0)else $error("carry_out should have a low value.");
   
   property check_a_min;
    @(posedge clk)(select == '0) && (a[WIDTH-1:0] == '0) |=> (out[WIDTH*2-1:0] == $past(b[WIDTH-1:0]));
   endproperty
   assert property (check_a_min) else $error("out should have 'b' value. out -> %0d, a -> %0d b -> %0d.", (out[WIDTH*2-1:0]),past_a, past_b);

   property check_b_min; 
    @(posedge clk)(select == '0) && (b[WIDTH-1:0] == 0) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]));
   endproperty
   assert property (check_b_min) else $error("out should have 'a' value.");

   property check_negative_result;
   @(posedge clk)(select == 3'b001) && (b[WIDTH-1:0] > a[WIDTH-1:0]) |=> (out[WIDTH*2-1:0] == $past(b[WIDTH-1:0]) - $past(a[WIDTH-1:0]));
   endproperty
   assert property (check_negative_result)else $error("SUBSTRACTOR has not donne the substraction b > a correctly.");
   
   property check_positive_result;
   @(posedge clk)(select == 3'b001) && (a[WIDTH-1:0] > b[WIDTH-1:0]) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]) - $past(b[WIDTH-1:0]));
   endproperty
   assert property (check_positive_result)else $error("SUBSTRACTOR has not donne the substraction a > b correctly.");
  /* 
   property check_sign_bit_pos;
    @(posedge clk)(select == 3'b001) && (a[WIDTH-1:0] > b[WIDTH-1:0]) |=> (sign_bit == 0);
    endproperty
   assert property (check_sign_bit_pos)else $error("sign bit is not positive");

   property check_sign_bit_negative;
    @(posedge clk)(select == 3'b001) && (b[WIDTH-1:0] > a[WIDTH-1:0]) |=> (sign_bit == 1);
    endproperty
   assert property (sign_bit == 1)else $error("sign bit is not negative");
*/
   property check_a_sub_0;
   @(posedge clk)(select == 3'b001) && (a[WIDTH-1:0] == 0) |=> (out[WIDTH*2-1:0] == $past(b[WIDTH-1:0]));
   endproperty
   assert property (check_a_sub_0)else $error("SUBSTRACTOR has an error with the substraction.");

   property check_b_sub_0;
   @(posedge clk) (select == 3'b001) && (b[WIDTH-1:0] == 0) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]));
   endproperty
   assert property (check_b_sub_0)else $error("SUBSTRACTOR has an error with the substraction.");

   property check_mult_result;
   @(posedge clk) (select == 3'b110) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]) * $past(b[WIDTH-1:0]));
   endproperty
   assert property (check_mult_result)else $error("MULTIPLICATOR has not done multiplication correctly.");
   
   property check_mult_by_zero;
   @(posedge clk) (select == 3'b110) && ((a[WIDTH-1:0] == 0) || (b[WIDTH-1:0] == 0)) |=> (out[WIDTH*2-1:0] == 0);
   endproperty
   assert property (check_mult_by_zero)else $error("The multiblication by zero should be zero.");
   
   property check_mult_a_1;
   @(posedge clk) (select == 3'b110) && (a[WIDTH-1:0] == 1) |=> (out[WIDTH*2-1:0] == $past(b[WIDTH-1:0]));
   endproperty
   assert property (check_mult_a_1)else $error("The multiblication result should be 'b'.");
   
   property check_mult_b_1;
   @(posedge clk) (select == 3'b110) && (b[WIDTH-1:0] == 1) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]));
   endproperty
   assert property (check_mult_b_1)else $error("The multiblication result should be 'a'.");
   
   property check_mult_pair_result;
   @(posedge clk) (select == 3'b110) && ((a[WIDTH-1:0] % 2 == 0) || (b[WIDTH-1:0] % 2 == 0)) |=> (out[WIDTH*2-1:0] % 2 == 0);
   endproperty
   assert property (check_mult_pair_result)else $error("The multiplication result should have been an even number.");
   
   property check_mult_unpair_result;
   @(posedge clk) (select == 3'b110) && ((a[WIDTH-1:0] % 2 == 1) && (b[WIDTH-1:0] % 2 == 1)) |=> (out[WIDTH*2-1:0] % 2 == 1) || (out[WIDTH*2-1:0] == 0);
   endproperty
   assert property (check_mult_unpair_result)else $error("The multiplication result should have been an odd number.");
   
   property check_div_result;
   @(posedge clk) (select == 3'b111) && (b[WIDTH-1:0] != 0) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]) / $past(b[WIDTH-1:0]));
   endproperty
   assert property (check_div_result)else $error("DIVIDER has not done division correctly.");
   
   property check_div_a_0;
   @(posedge clk) (select == 3'b111) && (a[WIDTH-1:0] == 0) && (b[WIDTH-1:0] != 0) |=> (out[WIDTH*2-1:0] == 0);
   endproperty
   assert property (check_div_a_0)else $error("The division result should have been 0.");
   
   property check_div_b_0;
   @(posedge clk) (select == 3'b111) && (b[WIDTH-1:0] == 0) |=> (inf == 1);
   endproperty
   assert property (check_div_b_0)else $error("The infinite flag should have been 1.");
   
   property check_div_b_1;
   @(posedge clk) (select == 3'b111) && (b[WIDTH-1:0] == 1) |=> (out[WIDTH*2-1:0] == $past(a[WIDTH-1:0]));
   endproperty
   assert property (check_div_b_1)else $error("The division result should have been 'a'.");
   
   property check_div_a_1;
   @(posedge clk) (select == 3'b111) && (a[WIDTH-1:0] == b[WIDTH-1:0]) && (b[WIDTH-1:0] != 0) |=> (out[WIDTH*2-1:0] == 1);
   endproperty
   assert property (check_div_a_1)else $error("The division result should have been 1.");
      
   property check_and;
   @(posedge clk) (select == 3'b010) |=>  (out[WIDTH*2-1:0] == ($past(a[WIDTH-1:0]) & $past(b[WIDTH-1:0])));
   endproperty
   assert property (check_and)else $error("output BITWISE AND sould be max value");   
   
   property check_all_and_0;
   @(posedge clk) (select == 3'b010) && ((a[WIDTH-1:0] == '0) || (b[WIDTH-1:0] == '0))|=>  (out[WIDTH*2-1:0] == '0);
   endproperty
   assert property (check_all_and_0)else $error("output BITWISE AND sould be max value");
   
   property check_all_and_1;
   @(posedge clk) (select == 3'b010) && ((a[WIDTH-1:0] == '1) || (b[WIDTH-1:0] == '1))|=>  (out[WIDTH*2-1:0] == '1);
   endproperty
   assert property (check_all_and_0)else $error("output BITWISE AND sould be 1.");

     
endinterface
