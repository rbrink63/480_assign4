//System Level Stuff
`define WORD  [15:0]
`define REGSIZE [15:0]
`define MEMSIZE [65535:0]
`define STATE [4:0]
`define PRESIZE [11:0]

//Instruction Encoding
`define CC      [15:14]
`define AL      2'b00
`define S       2'b01
`define EQ      2'b10
`define NE      2'b11
`define Opcode  [13:9]
`define isReg   [8]
`define Dest    [7:4]
`define Op2     [3:0]

//OPcodes
`define NOP             16'b0010111000000000
`define OPnop           5'b10111
`define OPpre           2'b00
`define OPpre		5'h00
`define OPadd		5'h08
`define OPand		5'h09
`define OPbic		5'h0a
`define OPeor		5'h0b
`define OPmul		5'h0c
`define OPorr		5'h0d
`define OPsha		5'h0e
`define OPslt		5'h0f
`define OPsub		5'h10
`define OPaddf		5'h11
`define OPftoi		5'h12
`define OPitof		5'h13
`define OPmulf		5'h14
`define OPrecf		5'h15
`define OPsubf		5'h16
`define OPmov		5'h17
`define OPneg		5'h18
`define OPldr		5'h19
`define OPstr		5'h1a
`define OPsys		5'b11111



module stageZero(PCchange,waitFlag,clk,reset,instOut,pc);

  input `WORD PCchange;
  input  waitFlag;
  input  clk;
  input reset;
  output reg `WORD instOut = `NOP;
  output reg `WORD pc;

  reg `WORD cycles = 0;  
  
  reg `WORD instrmem `MEMSIZE;
  reg `WORD pcStageZero = 0;
  reg firstWait = 0;

  always @(reset) begin
    $readmemh("instrmem.txt",instrmem,0,999);

  end

  always @(posedge clk) 
    begin
      if(PCchange != 0)
        begin
          pcStageZero <=  PCchange;
        end
      else if(waitFlag == 1)
        begin
          instOut  <= `NOP;
          pcStageZero <= pcStageZero - 2;
          cycles <= 5;
        end
      else if (cycles != 0)
        begin
          instOut  <= `NOP;
          cycles <= cycles - 1;
        end
      else
        begin
            instOut <= instrmem[pcStageZero];
            pcStageZero <= pcStageZero + 1;
        end
      pc <= pcStageZero;
    end

endmodule
 


module stageOne(clk ,reset, instIn, PC,registerWrite ,regToWrite, dataToReg,instOut, waitFlag, op2, Rd);
  input clk;
  input reset;
  input `WORD instIn;
  input `WORD PC;
  input registerWrite;
  input `REGSIZE regToWrite;
  input `WORD dataToReg;
  output reg `WORD instOut = `NOP;
  output reg waitFlag = 0;
  output reg `WORD op2;
  output reg `WORD Rd;

  reg `WORD regfile `REGSIZE;
  reg [3:0] stage2Reg, stage3Reg;
  reg [11:0] pre;
  
  always @(reset) begin
    regfile[15] = 0; 
    $readmemh("regfile.txt",regfile,0,15);

  end

  always @(posedge clk) 
    begin
      //instOut <= instIn; 
      $display("$time:%x  reg0:%x reg1:%x reg2:%x reg3:%x reg4:%x reg5:%x reg6:%x reg7:%x PC:%x reg13:%x",$time,regfile[0],regfile[1],regfile[2],regfile[3],regfile[4],regfile[5],regfile[6],regfile[7],PC, regfile[13] );
      regfile[15] <= PC;
      if(instIn `Opcode != `OPsys && instIn `Opcode != `OPpre && instIn != `NOP)
        begin
          stage3Reg <= stage2Reg;
          stage2Reg <= instIn `Dest;
        end
      else
        begin
          stage3Reg <= stage2Reg;
          stage2Reg <= 4'bxxxx;
        end
              
      
      if (((stage2Reg == instIn `Op2 ||  stage3Reg == instIn `Op2) || (stage2Reg == instIn `Dest ||  stage3Reg == instIn `Dest)) && (instIn `Opcode != `OPsys && instIn `Opcode != `OPpre && instIn != `NOP) && waitFlag == 1'b0)
        begin
          instOut  <= `NOP; 
          waitFlag <= 1'b1;
        end
      else if(waitFlag == 1'b1)
        begin
          instOut  <= `NOP;
          waitFlag <= 1'b0;
        end
      else
        begin
          waitFlag <= 1'b0;
          instOut <= instIn;
        end
    
      if((instIn `Opcode != `OPsys && instIn `Opcode != `OPpre && instIn != `NOP) && waitFlag == 0)
      begin
        case(instIn `isReg)
          1: begin op2 <= instIn `Op2;
                   Rd  <= regfile[instIn `Dest]; end
          0: begin op2 <= regfile[instIn `Op2];  
                   Rd  <= regfile[instIn `Dest]; end 
        endcase
      end
        
      if(registerWrite == 1)
        begin
          regfile[regToWrite] <= dataToReg;
        end

    end

endmodule


module stageTwo(clk,reset,instIn,Rd,op2In,instOut,result, op2Out,halt);
  input clk,reset;
  input `WORD instIn;
  input `WORD Rd, op2In;
  output reg `WORD instOut = `NOP;
  output reg `WORD result;
  output reg halt;
  output reg  `WORD op2Out;

  integer cycles = 2;  
  
  reg `WORD operand2;
  reg [11:0] pre;
  reg posFlag = 0;
  reg usePre = 0;

  always @(reset) begin
    halt = 0;
  end

  always @(posedge clk)
    begin

      instOut <= instIn;
      
      if(instIn [13:12] == `OPpre)
        begin
          usePre <= 1;
          pre <= instIn[11:0];
          if(instIn[11:0] == 0)
            begin
              posFlag <= 1;
            end
          else
            begin
              posFlag <= 0;
            end
        end
        
      else if(usePre == 1 && instIn != `NOP)
        begin
          operand2[15:4] = pre;
          operand2[3:0]  = op2In;
          usePre <= 0;
          pre <= 0;
        end
    

      else 
        begin
          if((instIn `Opcode != `OPldr && instIn `Opcode != `OPstr) && posFlag == 0 && instIn `isReg != 0)
            begin
              case(op2In[3])
                1'b0: begin operand2 = op2In; end
                1'b1: begin operand2[15:4] = 12'hfff; operand2[3:0] = op2In[3:0]; end
              endcase
            end
		  else
            begin
              operand2 = op2In;
            end
        end 
      if(instIn != `NOP && instIn[13:12] != `OPpre) begin
        case(instIn `Opcode)
          `OPadd: begin result  <= Rd + operand2; $display("$time:%x [2] Rd:%x + operand2:%x instIn:%x",$time,Rd,operand2,instIn); end
          `OPsub: begin result  <= Rd - operand2; $display("$time:%x [2] Rd:%x - operand2:%x instIn:%x",$time,Rd,operand2,instIn); end
          `OPand: begin result  <= Rd & operand2; end   
          `OPbic: begin result  <= Rd & ~(operand2); end
          `OPeor: begin result  <= Rd ^ (operand2); end
          `OPldr: begin result  <= operand2; end
          `OPmov: begin result  <= operand2; end
          `OPmul: begin result  <= Rd * (operand2); end
          `OPneg: begin result  <= -1 * (operand2); end 
          `OPorr: begin result  <= Rd | (operand2); end
          `OPsha: begin result  <= ((operand2 > 0) ? (Rd << operand2) : (Rd >> (-1 * operand2))); end
          `OPstr: begin result  <= Rd; op2Out<=operand2; end
          `OPslt: begin result  <= (Rd < (operand2)); end
          `OPsys: begin end
          default: begin instOut `Opcode <= `OPsys; instOut `CC <= instIn `CC; end
        endcase
      end
      
      
    end
    
endmodule


module stageThree(clk,reset, instIn, result,op2, registerWrite,regToWrite, dataToReg, PCchange,halt);
  input clk, reset;
  input `WORD instIn, result, op2;
  output reg `REGSIZE regToWrite;
  output reg `WORD dataToReg;
  output reg `WORD PCchange = 0;
  output reg registerWrite;
  output reg halt;

  reg `WORD datamem `MEMSIZE;
  reg Z;
  reg `WORD cycles = 0;
  reg haltFlag = 0;
  
  always @(posedge reset)
    begin
      halt = 0;
    end

  always @(posedge clk) 
    begin
            
      registerWrite <= 0;
      PCchange <= 0;
      if(instIn == `NOP || instIn[13:12] == `OPpre)
        begin
          registerWrite <=0;
        end
      
      else if(haltFlag == 1 && cycles != 0)
        begin 
          cycles <= cycles - 1;
        end
        
      else if(haltFlag == 1 && cycles == 0)
        begin
          halt <= 1;
        end
        
      else if(cycles != 0)
        begin
          cycles <= cycles - 1;
        end
      else if(instIn `CC == `S)
        begin
          case(result)
                  0: begin Z <= 1; end
            default: begin Z <= 0; end
          endcase
          
              case(instIn`Opcode)
                 `OPstr: begin datamem[op2] <= result;
                               registerWrite <= 0; end
                 `OPldr: begin regToWrite <= instIn `Dest;
                               dataToReg <= datamem[result];
                               registerWrite <= 1;$display("time:%x writing R%x = %x",$time, instIn `Dest ,result);end
                 `OPsys: begin haltFlag <= 1;cycles <= 2; end
                default: begin dataToReg <= result;
                               regToWrite <= instIn `Dest;
                               registerWrite <= 1; end
              endcase
        
          if(instIn `Dest == 15)
            begin
              PCchange <= result;
              cycles <= 2;
            end                     
        end

      else if(instIn `CC == `NE || instIn `CC == `EQ)
        begin
          if ((Z == 1 && instIn `CC == `NE) || (Z == 0 && instIn `CC == `EQ))
            begin
              case(instIn`Opcode)
                 `OPstr: begin datamem[op2] <= result;
                               registerWrite <= 0; end
                 `OPldr: begin regToWrite <= instIn `Dest;
                               dataToReg <= datamem[result];
                               registerWrite <= 1; end
                 `OPsys: begin haltFlag <= 1; cycles <= 2; end
                default: begin dataToReg <= result;
                               regToWrite <= instIn `Dest;
                               registerWrite <= 1; end
              endcase
        
            if(instIn `Dest == 15)
              begin
                PCchange <= result;
                cycles <= 2;
              end           
            end
        end
        
      else if(instIn `CC == `AL)
        begin
              case(instIn`Opcode)
                 `OPstr: begin datamem[op2] <= result;
                               registerWrite <= 0; end
                 `OPldr: begin regToWrite <= instIn `Dest;
                               dataToReg <= datamem[result];
                               registerWrite <= 1; end
                 `OPsys: begin haltFlag <= 1;cycles <= 2; end
                default: begin dataToReg <= result;
                               regToWrite <= instIn `Dest;
                               registerWrite <= 1; end
              endcase
        
          if(instIn `Dest == 15)
            begin
              PCchange <= result;
              cycles <= 2;
            end
        end
      else
        begin
          halt <= 1;
        end
    end

endmodule



module processor(halt, reset, clock);
  output wire halt;
  input reset, clock;


  wire `WORD PCchange;
  wire `WORD instOut0;// = `NOP;
  wire `WORD pc;
  wire  waitFlag;
  wire ir;
  wire `WORD op2;

  wire `WORD instOut1;// = `NOP;
  wire `WORD op2Data1;
  wire `WORD destData1;
  wire `REGSIZE regToWrite;

  wire `WORD instOut2;//= `NOP;
  wire `WORD result;
  
  wire `WORD  dataToReg, pcCHANGE;
  wire registerWrite;


    stageZero stage_zero(pcCHANGE,
                         waitFlag,
                         clock ,
                         reset,
                         instOut0,
                         pc);

    stageOne stage_one(clock,
                     reset,
                     instOut0, 
                     pc,
                     registerWrite, 
                     regToWrite, 
                     dataToReg,
                     instOut1, 
                     waitFlag, 
                     op2Data1, 
                     destData1);

    stageTwo  stage_two(clock,
                      reset,
                      instOut1, 
                      destData1,
                      op2Data1,
                      instOut2,
                      result,
                      op2,
                      halt); 

    stageThree stage_three(clock,
                       reset, 
                       instOut2, 
                       result,
                       op2, 
                       registerWrite,
                       regToWrite, 
                       dataToReg, 
                       pcCHANGE,
                       halt);
    always@(posedge clock)
      begin                                            
        $display("$time:%x [0]%x->[1]%x->[2]%x->[3] waitFlag:%x", $time,instOut0, instOut1, instOut2,waitFlag);
      end
  

endmodule

module testbench;
  reg reset = 0;
  reg clk = 0;
  wire halted;
  processor PE(halted, reset, clk);
  initial begin
   $dumpfile("dumpfile.vcd");
   $dumpvars(0,PE);
   #10 reset = 1;
   #10 reset = 0;
    while (!halted) begin
     #10 clk = 1;
     #10 clk = 0;
    end
    $finish;
  end
endmodule