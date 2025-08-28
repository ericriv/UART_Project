`define state uart_rx_tb.my_uart.state
`define bit_index uart_rx_tb.my_uart.bit_index
`define shifter uart_rx_tb.my_uart.shifter
`define sample_tick uart_rx_tb.my_uart.sample_tick

module uart_rx_sva #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input 	logic			rst_,
input	logic			rx_serial,
input	logic	[7:0]	rx_data,
input	logic			rx_valid,
input	logic			rx_error
);

property reset_check;
	@(posedge clk)
		(!rst_ |-> (rx_data == 0 && `state == uart_rx_tb.my_uart.IDLE && !rx_valid && !rx_error && `bit_index == 0 && `shifter == 0));
endproperty 
reset_checkP: assert property (reset_check) else $display($stime,"\t\t FAIL::reset_check\n");
reset_checkC: cover property (reset_check) $display($stime,"\t\t PASS::reset_check\n");

property start_check;
	@(posedge clk) disable iff(!rst_)
		(rx_serial |-> ##1 `state == uart_rx_tb.my_uart.START);
endproperty
start_checkP: assert property (start_check) else $display($stime,"\t\t FAIL::start_check\n");
start_checkC: cover property (start_check) $display($stime,"\t\t PASS::start_check\n");

property start_verif_check;
	@(posedge clk) disable iff(!rst_)
		((`sample_tick && `state == uart_rx_tb.my_uart.START && rx_serial) |-> ##1 (`state == uart_rx_tb.my_uart.IDLE && rx_error));
endproperty
start_verif_checkP: assert property (start_verif_check) else $display($stime,"\t\t FAIL::start_verif_check\n");
start_verif_checkC: cover property (start_verif_check) $display($stime,"\t\t PASS::start_verif_check\n");

property sample_align_check;
	@(posedge clk) disable iff(!rst_)
		((`state == uart_rx_tb.my_uart.DATA && `sample_tick) |-> ##1 `bit_index == ($past(`bit_index)+1));
endproperty
sample_align_checkP: assert property (sample_align_check) else $display($stime,"\t\t FAIL::sample_align_check\n");
sample_align_checkC: cover property (sample_align_check) $display($stime,"\t\t PASS::sample_align_check\n");

property sample_check;
	@(posedge clk) disable iff(!rst_)
		((`state == uart_rx_tb.my_uart.DATA && `sample_tick) |-> ##1 `shifter[7] == $past(rx_serial));
endproperty
sample_checkP: assert property (sample_check) else $display($stime,"\t\t FAIL::sample_check\n");
sample_checkC: cover property (sample_check) $display($stime,"\t\t PASS::sample_check\n");


property data_to_stop_check;
	@(posedge clk) disable iff(!rst_)
		((`state == uart_rx_tb.my_uart.DATA && `sample_tick && `bit_index == 3'b111) |-> ##1 `state == uart_rx_tb.my_uart.STOP);
endproperty
data_to_stop_checkP: assert property (data_to_stop_check) else $display($stime,"\t\t FAIL::data_to_stop_check\n");
data_to_stop_checkC: cover property (data_to_stop_check) $display($stime,"\t\t PASS::data_to_stop_check\n");

property stop_exit_check;
	@(posedge clk) disable iff (!rst_)
		((`state == uart_rx_tb.my_uart.STOP && `sample_tick) |-> ##1 (rx_valid ^ rx_error));
endproperty
stop_exit_checkP: assert property (stop_exit_check) else $display($stime,"\t\t FAIL::stop_exit_check\n");
stop_exit_checkC: cover property (stop_exit_check) $display($stime,"\t\t PASS::stop_exit_check\n");

endmodule 