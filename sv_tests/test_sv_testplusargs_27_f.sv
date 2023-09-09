//----------------------------------------------------
// SPDX-FileCopyrightText: Jayaraman R P,
//                         Verifworks Pvt Ltd,India
// SPDX-License-Identifier: MIT
//----------------------------------------------------
class test_args;

bit cpu,gpu;

if ($test$plusargs("ENABLE_CPU")) begin
  cpu=1;
  gpu=0;
end


if ($test$plusargs("ENABLE_CPU_WITH_GPU")) begin
  cpu=1;
  gpu=1;
end

endclass: test_args
