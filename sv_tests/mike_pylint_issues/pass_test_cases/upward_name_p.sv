module upward_name_p;

initial
        begin:TB_INITIAL
                reg signal;
        end

initial
        begin
                TB_INITIAL.signal = 0;//calling "signal" using the begin label "TB_INITIAL"
                $display("value of signal:%0d",TB_INITIAL.signal);
        end
endmodule