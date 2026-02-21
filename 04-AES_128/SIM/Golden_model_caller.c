#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "C:/questasim64_2021.1/include/svdpi.h"

void call_python_script() {
    int result = system("python Golden_model.py");
    if (result == -1) {
        printf("Error executing Python script");
    }
	else {
        // printf("Inside C function, calling python occured correctly\n");
    }
	return;
}
