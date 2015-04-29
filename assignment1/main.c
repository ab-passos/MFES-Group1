#include <stdio.h>
#include <stdlib.h>

#include "sensor.h"

/* global queue instance to be modified by the assignment functions */

extern sensor_t *sensor_result_queue;

void print_sensor(sensor_t *sensor);

int main()
{
	return 0;
}

void print_sensor(sensor_t *sensor)
{
	int aux = 0;
	for(int i = 0; i < CAPACITY; ++i)
	{
		printf("   %3d -> ", i);
		if(sensor->scan_results[i])
			printf("( %2d )", sensor->scan_results[i]->request_type);
		else
			printf("(null)");

		aux++;
		if(aux == 6){
			printf("\n");
			aux = 0;
		}

	}
}