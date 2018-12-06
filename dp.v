// basic sizes of things
`define DATA	[15:0]
`define ADDR	[15:0]
`define SIZE	[65535:0]
`define INST	[15:0]
`define CC	[15:14]
`define OP	[14:9]
`define IORR	[8]
`define RD	[7:4]
`define RN	[3:0]
`define REGS    [15:0]

// CC values
`define AL	0
`define S	1
`define NE	2
`define EQ	3

//Float defines
`define Fsign [15]
`define Fexp [14:7]
`define Fman [6:0]

// opcode values, also state numbers
`define OPPRE		5'h00
`define OPADD		5'h08
`define OPAND		5'h09
`define OPBIC		5'h0a
`define OPEOR		5'h0b
`define OPMUL		5'h0c
`define OPORR		5'h0d
`define OPSHA		5'h0e
`define OPSLT		5'h0f
`define OPSUB		5'h10
`define OPADDF		5'h11
`define OPFTOI		5'h12
`define OPITOF		5'h13
`define OPMULF		5'h14
`define OPRECF		5'h15
`define OPSUBF		5'h16
`define OPMOV		5'h17
`define OPNEG		5'h18
`define OPLDR		5'h19
`define OPSTR		5'h1a
`define OPSYS		5'h1f

// make NOP (after fetch) an unconditional PRE 0
`define NOP             16'b0

module processor(halt, reset, clk);
output reg halt;
input reset, clk;

reg `DATA r `REGS;	// register file
reg `DATA d `SIZE;	// data memory
reg `INST i `SIZE;	// instruction memory
reg `ADDR pc;		// program counter
reg `ADDR tpc, pc0, pc1;
reg `INST ir;		// instruction register
reg `INST ir0, ir1;
reg `DATA im0, rd1, rn1, res;
wire `DATA itof_res, ftoi_res, mulf_res, recf_res, addf_res, subf_res;
reg `ADDR target;	// jump target
reg jump;		// are we jumping?
reg zreg;		// z flag
wire pendz;		// z update pending?
wire pendpc;		// pc update pending?
reg wait1, wait2;		// need to stall in stage 1, or stage 2?
reg [11:0] prefix;	// 12-bit prefix value
reg havepre;		// is prefix valid?


int_to_float itof_mod(itof_res, rn1, clk);
float_to_int ftoi_mod(ftoi_res, rn1, clk);
mul_float mulf_mod(mulf_res, rd1, rn1, clk); 
recip_float recf_mod(recf_res, rn1, clk);
add_float addf_mod(addf_res, rd1, rn1, clk);
sub_float subf_mod(subf_res, rd1, rn1, clk);

always @(reset) begin
  halt = 0;
  pc = 0;
  ir0 = `NOP;
  ir1 = `NOP;
  jump = 0;
  havepre = 0;

// use the following with dollars to initialize
//readmemh0(r); // register file
  $readmemh("regfile.txt",r,0,15);
  $readmemh("instrmem.txt",i,0,999);
//readmemh1(d); // data memory
//readmemh2(i); // instruction memory
end

function setsrd;
input `INST inst;
setsrd = ((inst `OP >= `OPADD) && (inst `OP < `OPSTR));
endfunction

function setspc;
input `INST inst;
setspc = ((inst `RD == 15) && setsrd(inst));
endfunction

function setsz;
input `INST inst;
setsz = ((inst `CC == `S) && setsrd(inst));
endfunction

function iscond;
input `INST inst;
iscond = ((inst `CC == `NE) || (inst `CC == `EQ));
endfunction

function usesim;
input `INST inst;
usesim = ((inst `IORR) && (inst `OP <= `OPSTR));
endfunction

function usesrd;
input `INST inst;
usesrd = ((inst `OP == `OPADD) ||
          (inst `OP == `OPADDF) ||
          (inst `OP == `OPAND) ||
          (inst `OP == `OPBIC) ||
          (inst `OP == `OPEOR) ||
          (inst `OP == `OPMUL) ||
          (inst `OP == `OPMULF) ||
          (inst `OP == `OPORR) ||
          (inst `OP == `OPSHA) ||
          (inst `OP == `OPSTR) ||
          (inst `OP == `OPSLT) ||
          (inst `OP == `OPSUB) ||
          (inst `OP == `OPSUBF));
endfunction

function usesrn;
input `INST inst;
usesrn = ((!(inst `IORR)) && (inst `OP <= `OPSTR));
endfunction


// pending z update?
assign pendz = (setsz(ir0) || setsz(ir1));

// pending PC update?
assign pendpc = (setspc(ir0) || setspc(ir1));

// stage 0: instruction fetch and immediate extend
always @(posedge clk) begin
  tpc = (jump ? target : pc);

  if (wait1) begin
    // blocked by stage 1, so should not have a jump, but...
    pc <= tpc;
  end else begin
    // not blocked by stage 1
    ir = i[tpc];

    if (pendpc || (iscond(ir) && pendz)) begin
      // waiting... pc doesn't change
      ir0 <= `NOP;
      pc <= tpc;
    end else begin
      if (ir[13:12] == 0) begin
        // PRE operation
        havepre <= 1;
        prefix <= ir[11:0];
        ir0 <= `NOP;
      end else begin
        if (usesim(ir)) begin
          // extend immediate
          im0 <= {(havepre ? prefix : {12{ir[3]}}), ir `RN};
          havepre <= 0;
        end
        ir0 <= ir;
      end
      pc <= tpc + 1;
    end

    pc0 <= tpc;
  end
end

// stage 1: register read
always @(posedge clk) begin
    if (wait2 == 1'b1) begin 
	wait1 = 1;
    end
    else if ((ir0 != `NOP) &&
      setsrd(ir1) &&
      ((usesrd(ir0) && (ir0 `RD == ir1 `RD)) ||
       (usesrn(ir0) && (ir0 `RN == ir1 `RD)))) begin
    // stall waiting for register value
    wait1 = 1;
    ir1 <= `NOP;
  end else begin
    // all good, get operands (even if not needed)
    wait1 = 0;
    rd1 <= ((ir0 `RD == 15) ? pc0 : r[ir0 `RD]);
    rn1 <= (usesim(ir0) ? im0 :
            ((ir0 `RN == 15) ? pc0 : r[ir0 `RN]));
    ir1 <= ir0;
  end
end

// stage 2: ALU, data memory access, store in register
always @(posedge clk) begin
  if ((ir1 == `NOP) ||
      ((ir1 `CC == `EQ) && (zreg == 0)) ||
      ((ir1 `CC == `NE) && (zreg == 1))) begin
    // condition says nothing happens
    jump <= 0;
    wait2 <= 0;
 end else if (ir1 `OP >= 5'h11 && ir1 `OP <= 5'h16) begin
    //float operation, need to stall
     wait2 = 1;
     ir1 = `NOP;
  end else begin
    wait2 = 0;
    // let the instruction execute
    case (ir1 `OP)
      `OPPRE:  begin end // do nothing
      `OPADD:  res = rd1 + rn1;
      `OPAND:  res = rd1 & rn1;
      `OPBIC:  res = rd1 & ~rn1;
      `OPEOR:  res = rd1 ^ rn1;
      `OPMUL:  res = rd1 * rn1;
      `OPORR:  res = rd1 | rn1;
      `OPSHA:  res = ((rn1 > 0) ? (rd1 << rn1) : (rd1 >> -rn1));
      `OPSLT:  res = (rd1 < rn1);
      `OPSUB:  res = rd1 - rn1;
      `OPMOV:  res = rn1;
      `OPNEG:  res = -rn1;
      `OPLDR:  res = d[rn1];
      `OPSTR:  begin res = rd1; d[rn1] <= res; end
      //`OPADDF:
      //`OPFTOI:
      `OPITOF: begin res = itof_res; end
      //`OPMULF: 
      //`OPRECF: 
      //`OPSUBF: 
      default: halt <= 1; // make it stop
    endcase

    // update z flag if we should
    if (setsz(ir1)) zreg <= (res == 0);

    // put result in rd if we should
    if (setsrd(ir1)) begin
      if (ir1 `RD == 15) begin
        jump <= 1;
        target <= res;
      end else begin
        r[ir1 `RD] <= res;
        jump <= 0;
      end
    end else jump <= 0;
  end
end
endmodule


module add_float(out, a, b, clk);
    input `DATA a, b;
    input clk;
    output reg `DATA out;
    reg out_sign;
    reg [8:0] big_man, temp_man;
    reg [6:0] out_man;
    wire [8:0] small_man;
    reg [7:0] out_exp, big_exp, small_exp, shift_in, shift_amt;
    wire [7:0] shift_out;
    wire [7:0] a_exp, b_exp;
    wire [6:0] a_man, b_man;
    wire [4:0] num_zs;

    //just for viewing in GTKwave
    assign a_exp = a `Fexp;
    assign b_exp = b `Fexp;
    assign a_man = a `Fman;
    assign b_man = b `Fman;

    assign small_man = {2'b01, shift_out[6:0]};
    
    barrel_shift addf_bs(shift_out, shift_in, shift_amt);
    lead0s addf_zcount(num_zs,{temp_man, 7'h00});		

    always@(posedge clk)begin
	//if they're both 0 then output is 0
	if (a == 16'h0000 && b == 16'h0000) out = 16'h0000;
    	//if a is 0 then output is b
    	else if (a == 16'h0000) out = b;
    	//if b is 0 then output is a
    	else if (b == 16'h0000) out = a;
    	//otherwise do the thing
    	else begin

    	//barrel shift
	if (a `Fexp > b `Fexp)begin
	    shift_amt = a `Fexp - b `Fexp;
	    shift_in = b `Fman;
	    big_man = {2'b01, a `Fman};
	    big_exp = a `Fexp;
	    small_exp = b `Fexp;
	end else begin
	    shift_amt = b `Fexp - a `Fexp;
	    shift_in = a `Fman;
	    big_man = {2'b01, b `Fman};
	    big_exp = b `Fexp;
	    small_exp = a `Fexp;
	end

	//set output exponent to big_exp
//	out_exp = big_exp;

	//check signs
	if (a `Fsign == b `Fsign)begin
	    temp_man = big_man + small_man;
	    out_sign = a `Fsign; //either sign would work
	    if (temp_man[8])begin
		//overflow
		out_exp = big_exp + 1;
		out_man = temp_man[7:1];
	    end else begin
		out_man = temp_man[6:0];
	    end
	
	end else begin
	    //if signs are not equal 
	    temp_man = big_man - small_man;	
	    out_sign = (a `Fman > b`Fman) ? a `Fsign : b `Fsign;

	    out_man = temp_man << num_zs;
	end 
	


	
        end

	//out sign is handled above
	out `Fexp = out_exp;
	out `Fman = out_man;
    end

endmodule

//http://aggregate.org/EE480/slidesS1610.pdf
module barrel_shift(dst, src, shift);
output reg [7:0] dst; input wire [7:0] src, shift;
reg `DATA by1, by2, by4;
always @(*) begin
  by1 = (shift[0] ? {1'b0, src[7:1]} : src);
  by2 = (shift[1] ? {2'b0, by1[7:2]} : by1);
  by4 = (shift[2] ? {4'b0, by2[7:4]} : by2);
  dst = (shift[7:3] ? 0 : by4);
end
endmodule

module sub_float(out, a, b, clk);
    input `DATA a, b;
    input clk;
    output reg `DATA out;
    reg out_sign;
    reg [6:0] out_man;
    reg [7:0] out_exp;

endmodule

module recip_float(out, in, clk);
    input `DATA in;
    input clk;
    output reg `DATA out;
    reg [7:0] buff;
    reg [7:0] lookup[0:127];
    reg [6:0] out_man;
    reg [7:0] out_exp;


    initial begin
	$readmemh("recf_lookup.txt",lookup,0,127);
    end

    always @(posedge clk) begin
	if(in == 16'h0000)begin
	 	out = 16'h0000;
    	end else begin
	   if(in[6:0] == 0) begin //checks mantissa for zeros 
    	   out_exp = 254 - (in `Fexp);
    	   end
	   else begin
    	   out_exp = 253 - (in `Fexp);
    	   end
    	   
	   case(in `Fman)
    	   7'b1: begin out_man = lookup[126]; end
    	   default: begin  buff[7:0] = lookup[in `Fman]; out_man = buff [7:1]; end
       	   endcase

	   end
	    
	   out `Fsign = in `Fsign;
	   out `Fexp = out_exp;
	   out `Fman = out_man;
    end
endmodule

module mul_float(out, a, b, clk);
    input `DATA a, b;
    input clk;
    output reg `DATA out;

    reg [7:0] temp_exponent;
    reg `DATA temp_mantissa; //result of multiplying two 8bit nums could be as large as 16 bits

    reg [6:0] out_man;
    reg [7:0] out_exp;

    wire diff_sign;

    //check if the sign of the operands is different
    assign diff_sign = a `Fsign ^ b `Fsign;
    //if diff_sign == 1 then the output is neg
    //if diff_sign == 0 then the output is pos
   
    always @ (posedge clk)begin
	//if (a == 16'h0 || b == 16'h0)begin
	//    out = 16'h0;	
    	//end
	//else begin
	    //add exponents
    	    temp_exponent = a `Fexp  + b `Fexp;
    	    
    	    //multiply mantissas
    	    //add in implicit 1 at the top of the mantissa before multiplication
    	    temp_mantissa = {1'b1, a `Fman} * {1'b1, b `Fman};

	    case (temp_mantissa[15])
		1'b0: begin out_exp = temp_exponent - 127; out_man = temp_mantissa[13:7]; end
		//add 1 to  exp if there is an overflow in mantissa
		//multiplication
		1'b1: begin out_exp = temp_exponent - 126; out_man = temp_mantissa[14:8]; end
	    endcase

	    out `Fsign = diff_sign;
	    out `Fexp = out_exp;
	    out `Fman = out_man;
	    		    
//	end    	
    end
endmodule

module float_to_int(out, in, clk);
	input `DATA in;
	input clk;
	output reg `DATA out, out_temp;
	wire `DATA shifted_result;

	wire sign;
	reg [7:0] exponent;
	reg [22:0] mantissa, left_shift, right_shift;
	reg `DATA exp_less_bias;
	
	reg [15:0] man_pad;

	initial begin	
	    man_pad = 16'h1;
	end	
	
	assign sign = in `Fsign;

	always @ (posedge clk)begin
	    //take positive 8bit fraction part
	    exponent = in `Fexp;
	    mantissa = {man_pad, in `Fman};
	    exp_less_bias = exponent - 127;
	    left_shift = mantissa << exp_less_bias;

            out_temp = {(exp_less_bias > 0) ? left_shift[22:7] : 22'h0};

	    if (sign)begin 
		out = (out_temp ^ 16'hFFFF) + 1'b1;
	    end else begin
		out = out_temp;
	    end

	end
endmodule

module int_to_float(out, in, clk);
	input `DATA in;
	input clk;
	output reg `DATA out;
	
	wire [4:0] d;	
	reg [6:0] extra_zeros;
	reg [22:0] in_plus_zeros, twos_in_plus_zeros;
	wire `DATA zero_count_input;
	
	//module lead0s(d, s);
	lead0s zero_counter(d,zero_count_input);		

	//need regs for components of float
	wire sign;
	reg [7:0] exponent;
	reg [6:0] mantissa;

	assign sign = in `Fsign;
	assign zero_count_input = {(sign == 1) ? ((in ^ 16'hFFFF) + 1'b1) : in};
	

	initial begin
		//we need these because worst case we have the int 1 which would have 15 leading zeros
		//so we grab the 1 and need 7 more bits
		extra_zeros = 7'b0;
	end	
	
	always @(posedge clk) begin
		if(in == 16'h0000) begin
			out = 16'h0000;
		end
		else begin
			
			//from Dietz's notes: take the most significant 1 + 7 more bits
			//so we need to count leading zeros
			in_plus_zeros = {in,extra_zeros};
			twos_in_plus_zeros = {((in ^ 16'hFFFF) + 16'h0001),extra_zeros};
		
			//positive and negative ints need to handled differently	
			case(sign)
				1'b0: begin mantissa = in_plus_zeros >> (15-d); end
				//1'b1: begin mantissa = (twos_in_plus_zeros >> (15-d)) + 1'b1; end
				1'b1: begin mantissa = twos_in_plus_zeros >> (15-d); end
			endcase
			
			//set exponent
			exponent = 127 + (15-d);

			out = {sign, exponent, mantissa};
		end
			
	end
endmodule

module lead0s(d, s);
	output reg[4:0] d; input wire[15:0] s;
	reg[7:0] s8; reg[3:0] s4; reg[1:0] s2;
	
	always @(*) begin
		if (s[15:0] == 0) d = 16; else begin
		d[4] = 0;
		{d[3],s8} = ((|s[15:8]) ? {1'b0,s[15:8]} : {1'b1,s[7:0]}); 
		{d[2],s4} = ((|s8[7:4]) ? {1'b0,s8[7:4]} : {1'b1,s8[3:0]}); 
		{d[1],s2} = ((|s4[3:2]) ? {1'b0,s4[3:2]} : {1'b1,s4[1:0]}); 
		d[0] = !s2[1];
		end 
	end
endmodule

module testbench;
reg reset = 0;
reg clk = 0;
wire halted;
processor PE(halted, reset, clk);
initial begin
  $dumpfile("dumpfile.vcd");
  $dumpvars(0, PE);
  #10 reset = 1;
  #10 reset = 0;
  while (!halted) begin
    #10 clk = 1;
    #10 clk = 0;
  end
  $finish;
end
endmodule


