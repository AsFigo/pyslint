xelab -dpiheader file.h -svlog test.sv
xsc file.c
xelab -svlog test.sv -sv_lib dpi -R
file.h
/**********************************************************************/
/* ____ ____ */
/* / /\/ / */
/* /___/ \ / */
/* \ \ \/ */
/* \ \ Copyright (c) 2003-2013 Xilinx, Inc. */
/* / / All Right Reserved. */
/* /---/ /\ */
/* \ \ / \ */
/* \___\/\___\ */
/**********************************************************************/
/* NOTE: DO NOT EDIT. AUTOMATICALLY GENERATED FILE. CHANGES WILL BE LOST. */
#ifndef DPI_H
#define DPI_H
#ifdef __cplusplus
#define DPI_LINKER_DECL extern "C"
#else
#define DPI_LINKER_DECL
#endif
#include "svdpi.h"
/* Exported (from SV) function */
DPI_LINKER_DECL DPI_DLLISPEC
int c_exported_func(
int x, int y);
/* Imported (by SV) function */
DPI_LINKER_DECL DPI_DLLESPEC
int cfunc(
int a, int b);
#endif
