interface alu_if #(parameter WIDTH = 4, n_alu = 4)(input clk);
  logic [WIDTH*n_alu-1:0] a;
  logic [WIDTH*n_alu-1:0] b;
  logic [2:0] select;
  logic a_greater, a_equal, a_less;
  logic [WIDTH*n_alu*8-1:0] out;
  logic [0:0] carry_out;
  logic arst;

  // BFM for stimuli
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
  endfunction
  
  function automatic b_random();
  std::randomize(b);
  endfunction
  
  function automatic b_greater_a_random();
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
  // BFM for testing
  // Coverage
  // Assertions

endinterface
