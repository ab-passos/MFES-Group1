#ifndef _SENSOR_H
#define _SENSOR_H

typedef struct {
    double from;
    double to;
} SENSOR_request_scan_x_t;

typedef struct {
    double value1;
    double value2;
} SENSOR_A_get_result_x_t;

typedef struct {
    double from;
    double to;
    double speed;
} SENSOR_request_scan_y_t;

typedef struct {
    double value1;
    double value2;
    double value3;
} SENSOR_A_get_result_y_t;

/* A tagged union to encapsulate the different results obtained from sensor A */

#define REQUEST_TYPE int
#define REQUEST_X 0
#define REQUEST_Y 1

typedef struct 
{
    REQUEST_TYPE request_type;
    union
    {
        SENSOR_A_get_result_x_t *result_x;
        SENSOR_A_get_result_y_t *result_y;
    };
} scan_result_t;

#define RESPONSE int
#define OK 0
#define ERROR_SCAN_A 1
#define ERROR_GET_SCAN_A 2

RESPONSE SENSOR_A_request_x (const SENSOR_request_scan_x_t *params_p, int *id_p);
RESPONSE SENSOR_A_get_result_scan_x (int id, SENSOR_A_get_result_x_t *params_p);

RESPONSE SENSOR_A_request_y(const SENSOR_request_scan_y_t *params_p, int *id_p);
RESPONSE SENSOR_A_get_result_scan_y(int id, SENSOR_A_get_result_y_t *params_p);

typedef struct s_list_node
{
    int id;
    scan_result_t *scan_result;

    struct s_list_node *next;
} *s_list;

typedef struct 
{
    int nextID;

    int size;
    int capacity;

    s_list list;
} s_queue_t;

/* linked list */
void delete_list(s_list list);

s_list list_push(s_list list, int id, scan_result_t *result);
s_list list_get(s_list list, int id, scan_result_t **result);

/* linked-list backed queue */
s_queue_t *new_queue(int max);
void delete_queue(s_queue_t *queue);

int push_result(s_queue_t *queue, scan_result_t *result, int * id);
int get_result(s_queue_t *queue, int id, scan_result_t **results);

void show_queue(s_queue_t *queue);
void show_scan_result(scan_result_t *scan_result);

void show_queue(s_queue_t *queue);

/* global queue instance to be modified by the assignment functions */

s_queue_t *sensor_result_queue;

#endif
