interface alu_if #(parameter WIDTH = 4, n_alu = 4)(input clk);
  logic [WIDTH*n_alu-1:0] a;
  logic [WIDTH*n_alu-1:0] b;
  logic [2:0] select;
  logic a_greater, a_equal, a_less;
  logic [WIDTH*n_alu*8-1:0] out;
  logic [0:0] carry_out;
  logic enable;
  logic arst;

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


  //-------------------------------------------- Coverage ------------------------------------------------
  
  
  //------------------------------------------- Assertions -----------------------------------------------
  
  
  function check_sum();
   assert  (out == a + b)else begin
   $error("ADDER has not donne the sum correctly.");
   end
   endfunction
   
   function check_carry _out_1();
    if ((b + a) > WIDTH*WIDTH-1)
   assert  (carry_out > 0)else begin
   $error("carry_out should have a high value");
   end
   endfunction

   function check_carry_out_0();
    if ((b + a) <= WIDTH*WIDTH-1)
   assert  (carry_out > 0)else begin
   $error("carry_out should have a low value");
   end
   endfunction

   function check_a_min();
    if (a == 0)
   assert  (out == b)else begin
   $error("out should have 'b' value");
   end
   endfunction

   function check_b_min();
    if (b == 0)
   assert  (out == b)else begin
   $error("out should have 'a' value");
   end
   endfunction

   function check_negative_result();
    if (b > a)
   assert  (out == b - a)else begin
   $error("SUBSTRACTOR has not donne the substraction b > a correctly ");
   end
   endfunction
   
   function check_positive_result();
    if (a > b)
   assert  (out == a - b)else begin
   $error("SUBSTRACTOR has not donne the substraction a > b correctly ");
   end
   endfunction
   
   /*function check_sign_bit_pos();
    if (a > b)
   assert  (sign_bit == 0)else begin
   $error("sign bit is not positive");
   end
   endfunction
*/
   /*function check_sign_bit_negative();
    if (b > a)
   assert  (sign_bit == 1)else begin
   $error("sign bit is not negative");
   end
   endfunction
*/
   function check_a_sub_0();
    if (a == 0)
   assert  (out == b)else begin
   $error("SUBSTRACTOR has an error with the substraction");
   end
   endfunction
   
   function check_b_sub_0();
    if (b == 0)
   assert  (out == a)else begin
   $error("SUBSTRACTOR has an error with the substraction");
   end
   endfunction
   
   function check_mult_result();
   assert  (out == a * b)else begin
   $error("MULTIPLICATOR has not done multiplication correctly");
   end
   endfunction
   
   function check_mult_by_zero();
    if ((b == 0) || (a == 0))
   assert  (out == 0)else begin
   $error("The multiblication by zero should be zero");
   end
   endfunction
   
   function check_mult_a_1();
    if (a == 1)
   assert  (out == b)else begin
   $error("The multiblication result should be 'b'");
   end
   endfunction
   
   function check_mult_b_1();
    if (b == 1)
   assert  (out == a)else begin
   $error("The multiblication result should be 'a'");
   end
   endfunction
   
   function check_mult_pair_result();
    if ((b % 2 == 0) || (a % 2 == 0))
   assert  (out % 2 == 0)else begin
   $error("The multiplicatión result should have been an even number");
   end
   endfunction
   
   function check_mult_unpair_result();
    if ((b % 2 == 1) && (a % 2 == 1))
   assert  (out % 2 == 1)else begin
   $error("The multiplicatión result should have been an odd number");
   end
   endfunction
endinterface
