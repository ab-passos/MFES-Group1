#include <stdio.h>
#include <stdlib.h>

#include "sensor.h"

/* global queue instance to be modified by the assignment functions */

extern sensor_t *sensor_result_queue;



void print_sensor(sensor_t *sensor);

int main()
{
	sensor_t sensor;

	init_sensor(&sensor);

	scan_result_t result;

	result.id = 1;
	result.request_type = REQUEST_X;
	result.result_x = (SENSOR_A_get_result_x_t *) malloc (sizeof(SENSOR_A_get_result_x_t));

	result.result_x->value1 = 0.0f;
	result.result_x->value2 = 0.1f;

	add_result(&sensor, &result);

	scan_result_t *da_result = NULL;
	get_result(&sensor, 2, &da_result, REQUEST_X);

	printf("Did it work? %d\n", da_result != NULL);

	print_sensor(&sensor);

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