//uvm_driver without parameter(#(alu_sequence_item))
class alu_driver extends uvm_driver;
  `uvm_component_utils_begin(alu_driver)
  `uvm_component_utils_end
  
  virtual alu_interface vif;
  alu_sequence_item txn;
  
  function new(string name="alu_driver", uvm_component parent);
     super.new(name,parent);
    `uvm_info("DRIVER_CLASS","inside constructor",UVM_HIGH);
  endfunction: new
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRIVER_CLASS","Build Phase",UVM_HIGH);
       
    if(!(uvm_config_db#(virtual alu_interface)::get(this,"*","vif",vif)))
      begin 
        `uvm_fatal("DRIVER_CLASS","Failed to get VIF from the config DB");
      end
  endfunction: build_phase
      
   function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
     `uvm_info("DRIVER_CLASS","connect Phase",UVM_HIGH);
   endfunction: connect_phase
  
   task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRIVER_CLASS","run Phase",UVM_HIGH);
    txn = alu_sequence_item::type_id::create("txn");
    forever begin
    seq_item_port.get_next_item(txn);
    //Logic
    drive(txn);
    seq_item_port.item_done();
    end
    endtask: run_phase
  
  //-----------------
  //drive task
  //-----------------
  task drive(alu_sequence_item txn);//since it is an object pass by reference
    @(posedge vif.clock)
    //txn items are passed/driving to the interface
    vif.reset<=txn.reset;//use nonblocking in driver
    vif.a<=txn.a;
    vif.b<=txn.b;
    vif.op_code<=txn.op_code;
  endtask: drive
  
endclass: alu_driver


Error Log:
=========
vlog -writetoplevels questa.tops -timescale 1ns/1ns "+incdir+/playground_lib/uvm-1.2/src" -L /usr/share/questa/questasim//uvm-1.2 design.sv testbench.sv 
** Error: (vlog-13069) testbench.sv(5): near "uvm_driver": syntax error, unexpected IDENTIFIER.
** Error: testbench.sv(5): Error in class extension specification.
End time: 07:44:44 on Sep 11,2023, Elapsed time: 0:00:00
Errors: 2, Warnings: 0
