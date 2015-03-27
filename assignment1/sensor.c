#include "sensor.h"

#include <stdlib.h>

// show_queue
#include <stdio.h>

extern s_queue_t *sensor_result_queue;

/* Simple linked link implementation */

/* Free every element */
void delete_list(s_list list)
{
	if (!list)
		return;

	s_list next = list->next;
	free(list->scan_result);
	free(list);

	delete_list(next);
}

/* Insert at list head */
s_list list_push(s_list list, int id, scan_result_t *result)
{
	s_list new_list = (s_list) malloc (sizeof (struct s_list_node));

	new_list->id = id;
	new_list->scan_result = result;
	new_list->next = list;

	return new_list;
}

/* if the id is present assign the result and remove the node */
s_list list_get(s_list list, int id, scan_result_t **result)
{
	if(!list || !result)
		return NULL;

	if(list->id == id)
	{
		*result = list->scan_result;

		s_list next = list->next;
		free(list);

		return next;
	}

	list->next = list_get(list->next, id, result);
	return list;
}

/* simple queue backed by linked list */

/* Allocate a queue and initialise attributes */
s_queue_t *new_queue(int capacity)
{
	s_queue_t *queue = (s_queue_t *) malloc (sizeof (s_queue_t));
	queue->nextID = 0;

    queue->size = 0;
    queue->capacity = capacity;

    queue->list = NULL;

    return queue;
}

/* Clean-up */
void delete_queue(s_queue_t *queue)
{
	delete_list(queue->list);
	free(queue);
}

/* Add new result to queue */

int push_result(s_queue_t *queue, scan_result_t *result, int * id)
{
	if (queue->size >= queue->capacity || !id )
		return -1;

	queue->list = list_push(queue->list, queue->nextID, result);

	*id = queue->nextID;
	queue->nextID++;
	queue->size++;

	return 0;
}

/* Get result from queue */

int get_result(s_queue_t *queue, int id, scan_result_t **result)
{
	if(!queue || *result != NULL)
		return -1;

	queue->list = list_get(queue->list, id, result);

	if(!*result)
		return -1;

	queue->size--;
	return 0;
}

/* Ensure the element with given id is of the given type, RESULT_X or RESULT_Y */

int check_result_type(s_queue_t *queue, REQUEST_TYPE type, int id)
{
	s_list list = queue->list;

	while(list && list->id != id)
		list = list->next;
	
	if(!list || list->scan_result->request_type != type)
		return -1;
	
	return OK;
}

/* Assignment functions implementation */

/* Assuming requests are completed imediately */

RESPONSE SENSOR_A_request_x (const SENSOR_request_scan_x_t *params_p, int *id_p)
{
	/* Check for free space Example: request_cout < 200 */

	if(sensor_result_queue->size >= sensor_result_queue->capacity)
	{
		return ERROR_SCAN_A;
	}

	/*
		Do something with params_p
	*/

	SENSOR_A_get_result_x_t *scan_result_x = (SENSOR_A_get_result_x_t *) malloc (sizeof (SENSOR_A_get_result_x_t));

	scan_result_x->value1 = /* ... */ 0.0f;
	scan_result_x->value2 = /* ... */ 0.0f;

	scan_result_t *scan_result = (scan_result_t *) malloc (sizeof (scan_result_t));

	/* Tag it as a X result */
	scan_result->request_type = REQUEST_X;

	/* Assign nested structure */
	scan_result->result_x = scan_result_x;

	/* Push result onto the global queue */
	push_result(sensor_result_queue, scan_result, id_p);

	return OK;
}

RESPONSE SENSOR_A_get_result_scan_x (int id, SENSOR_A_get_result_x_t *params_p)
{
	// test if id maps a RESULT X
	if(check_result_type(sensor_result_queue,REQUEST_X, id) < 0)
	{
		return ERROR_GET_SCAN_A;
	}

	scan_result_t *scan_result_temp = NULL;

	get_result(sensor_result_queue, id, &scan_result_temp);

	return OK;
}



RESPONSE SENSOR_A_request_y(const SENSOR_request_scan_y_t *params_p, int *id_p)
{
	/* Check for free space: request_cout < 200 */

	if(sensor_result_queue->size >= sensor_result_queue->capacity)
	{
		return ERROR_SCAN_A;
	}

	/*
		Do something with params_p
	*/

	SENSOR_A_get_result_y_t *scan_result_y = (SENSOR_A_get_result_y_t *) malloc (sizeof (SENSOR_A_get_result_y_t));

	scan_result_y->value1 = /* ... */ 0.0f;
	scan_result_y->value2 = /* ... */ 0.0f;
	scan_result_y->value3 = /* ... */ 0.0f;

	scan_result_t *scan_result = (scan_result_t *) malloc (sizeof (scan_result_t));

	/* Tag it as a Y result */
	scan_result->request_type = REQUEST_Y;

	/* Assign nested structure */
	scan_result->result_y = scan_result_y;

	/* Push result onto the global queue */
	push_result(sensor_result_queue, scan_result, id_p);

	return OK;
}

RESPONSE SENSOR_A_get_result_scan_y(int id, SENSOR_A_get_result_y_t *params_p)
{
	// test if id maps a RESULT X
	if(check_result_type(sensor_result_queue,REQUEST_Y,id) < 0)
	{
		return ERROR_GET_SCAN_A;
	}


	scan_result_t *scan_result_temp = NULL;

	get_result(sensor_result_queue, id, &scan_result_temp);

	return OK;
}

/* Helper method to display queue */
void show_queue(s_queue_t *queue)
{
	if(!queue)
		return;

	printf("int nextID : %d \n" , queue->nextID);
    printf("int size : %d \n" , queue->size);
    printf("int capacity : %d \n" , queue->capacity);

    s_list aux = queue->list;

    scan_result_t *scan_result;

    while(aux)
    {
    	scan_result = aux->scan_result;

    	if(scan_result)
    	{	
			switch (scan_result->request_type)
			{
				case REQUEST_X:
    				printf("	[%3d] - Scan Result X(%f, %f)\n", aux->id,
															   scan_result->result_y->value1,
															   scan_result->result_y->value2);
					break;
				case REQUEST_Y:
					printf("	[%3d] - Scan Result Y(%f, %f, %f)", aux->id,
															   scan_result->result_y->value1,
															   scan_result->result_y->value2,
															   scan_result->result_y->value3);
					break;
			}
		}

    	aux = aux->next;
    }
}