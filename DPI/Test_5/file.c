#include "vpi_used.h"
#include "sv_auto-hdrs_for_c.h"

DPI_DLLESPEC
int gen_val_in_c(
      int *addr,
	  int *data)
{
  *addr = 11;
  *data = 22;
  printf("CVC: C: addr: 0x%x data: 0x%x \n ",*addr,*data);
  return 0;
}
