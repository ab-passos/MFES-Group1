#include <stdio.h>
#include <stdlib.h>
#include "sensor.h"

#define MAX_QUEUE 200


// The global queue defined in sensor.h
extern s_queue_t *sensor_result_queue;

int main(int argc, char *argv[])
{
	sensor_result_queue = new_queue(MAX_QUEUE);

	int *i = &argc;

	// initial queue test

	SENSOR_A_get_result_y_t *scan_result_y = (SENSOR_A_get_result_y_t *) malloc (sizeof (SENSOR_A_get_result_y_t));

	scan_result_y->value1 = /* ... */ 3.0f;
	scan_result_y->value2 = /* ... */ 2.0f;
	scan_result_y->value3 = /* ... */ 1.0f;

	scan_result_t *scan_result1 = (scan_result_t *) malloc (sizeof (scan_result_t));

	/* Tag it as a Y result */
	scan_result1->request_type = REQUEST_Y;
	scan_result1->result_y = scan_result_y;


	SENSOR_A_get_result_x_t *scan_result_x = (SENSOR_A_get_result_x_t *) malloc (sizeof (SENSOR_A_get_result_x_t));

	scan_result_x->value1 = /* ... */ 0.0f;
	scan_result_x->value2 = /* ... */ 0.0f;

	scan_result_t *scan_result2 = (scan_result_t *) malloc (sizeof (scan_result_t));

	/* Tag it as a X result */
	scan_result2->request_type = REQUEST_X;
	/* Assign nested structure */
	scan_result2->result_x = scan_result_x;

	push_result(sensor_result_queue, scan_result1, i);
	push_result(sensor_result_queue, scan_result2, i);

	// Assignment functions test

	SENSOR_A_get_result_y_t *params_p = (SENSOR_A_get_result_y_t *) malloc (sizeof (SENSOR_A_get_result_y_t));
	printf("[%d]\n", SENSOR_A_get_result_scan_y(0, params_p));

	SENSOR_A_get_result_x_t *params_p_2 = (SENSOR_A_get_result_x_t *) malloc (sizeof (SENSOR_A_get_result_x_t));
	printf("[%d]\n", SENSOR_A_get_result_scan_x(2, params_p_2));

	show_queue(sensor_result_queue);

	return 0;
}