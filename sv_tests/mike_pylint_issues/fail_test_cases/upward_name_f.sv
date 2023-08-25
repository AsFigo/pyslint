module upward_name_f;

initial
        begin:TB_INITIAL
                reg signal;
        end

initial
        begin
                signal=0;//scope for the "signal" is not visible here
                $display("value of signal:%0d",signal);
        end
endmodule