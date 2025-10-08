
class uart_tx_monitor extends uvm_component;

	`uvm_component_utils(uart_tx_monitor)
	
	uvm_analysis_port#(uart_tx_txn) ap;
	
	virtual uart_tx_if vif;
	int baud_divisor;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		ap = new("analysis_port", this);
	endfunction
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db#(virtual uart_tx_if)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF", "virtual interface not found!")
		if (!uvm_config_db#(int)::get(this, "", "baud_divisor", baud_divisor))
			`uvm_fatal("MON", "Baud divisor not set")
	endfunction
	
	task run_phase(uvm_phase phase);
		int tick_cnt = 0;
		uart_tx_txn tr;
		bit [7:0] data_byte;
		bit collecting;
		int bit_index;
		
		forever begin
			@(posedge vif.clk);
			
			if(!vif.rst_) begin
				tick_cnt = 0;
				collecting = 0;
				bit_index = 0;
			end
			
			else if(vif.tx_start)
				tick_cnt = 0;
			
			else if(vif.tx_busy) begin
				tick_cnt++;
				if(tick_cnt == baud_divisor/2) begin
					//tick_cnt = 0;
					if(!collecting && vif.tx_serial == 0) begin
						//start bit
						collecting = 1;
						data_byte = '0;
						bit_index = 0;
					end
					else if(collecting) begin
						bit_index++;
						if(bit_index >=1 && bit_index <= 8)
							data_byte[bit_index-1] = vif.tx_serial;
						else if(bit_index == 9) begin
							//stop bit detected
							collecting = 0;
							tr = uart_tx_txn::type_id::create("tr");
							tr.data = data_byte;
							ap.write(tr);
						end
					end
				end
				else if(tick_cnt == baud_divisor)
					tick_cnt = 0;
			end
		end 
	endtask
	
	
endclass