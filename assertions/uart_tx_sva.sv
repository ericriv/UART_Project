`define state uart_tx_tb.my_uart.state
`define	baud_cnt uart_tx_tb.my_uart.baud_cnt
`define	bit_index uart_tx_tb.my_uart.bit_index
`define	shifter uart_tx_tb.my_uart.shifter
`define	baud_tick uart_tx_tb.my_uart.baud_tick

module uart_tx_sva #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input	logic			rst_,
input	logic			tx_start,
input	logic	[7:0]	tx_data,
input	logic			tx_serial,
input	logic			tx_busy
);

localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;

property reset_check;
	@(posedge clk)
		(!rst_ |-> (tx_serial && !tx_busy && `state == 2'b0 && `baud_cnt == 0 && `shifter == 0 && `bit_index == 0));
endproperty
reset_checkP: assert property (reset_check) else $display($stime,"\t\t FAIL::reset_check\n");
reset_checkC: cover property (reset_check) $display($stime,"\t\t PASS::reset_check\n");

property idle_high_check;
	@(posedge clk) disable iff(!rst_)
		(!tx_busy |-> tx_serial);
endproperty
idle_high_checkP: assert property (idle_high_check) else $display($stime,"\t\t FAIL::idle_high_check\n");
idle_high_checkC: cover property (idle_high_check) $display($stime,"\t\t PASS::idle_high_check\n");

property start_bit_check;
	@(posedge clk) disable iff(!rst_)
		(`baud_tick && `state == 2'b01 |-> !tx_serial);
endproperty
start_bit_checkP: assert property (start_bit_check) else $display($stime,"\t\t FAIL::start_bit_check\n");
start_bit_checkC: cover property (start_bit_check) $display($stime,"\t\t PASS::start_bit_check\n");

property stop_bit_check;
	@(posedge clk) disable iff(!rst_)
		(`baud_tick && `state == 2'b11 |-> tx_serial);
endproperty
stop_bit_checkP: assert property (stop_bit_check) else $display($stime,"\t\t FAIL::stop_bit_check\n");
stop_bit_checkC: cover property (stop_bit_check) $display($stime,"\t\t PASS::stop_bit_check\n");

endmodule 