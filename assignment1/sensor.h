#ifndef __SENSOR_H
#define __SENSOR_H

#define CAPACITY 200

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
    int id;
    REQUEST_TYPE request_type;
    union
    {
        SENSOR_A_get_result_x_t *result_x;
        SENSOR_A_get_result_y_t *result_y;
    };
} scan_result_t;

typedef struct 
{
	scan_result_t *scan_results[CAPACITY];
    unsigned int size;

} sensor_t;

// Axioms:
    //@ logic unsigned int Capacity = (unsigned int) 200;
    //@ logic unsigned int Size{L}(sensor_t* s) = s->size;
    //@ logic scan_result_t** Storage{L}(sensor_t* s) = (scan_result_t**) s->scan_results;

// Predicates:
    //@ predicate Empty{L}(sensor_t* s) = Size(s) == 0;
    //@ predicate Full{L}(sensor_t* s) = Size(s) == Capacity;

/*@
// tests if every cell of the array is unchanged 
predicate
    Unchanged{A,B}(sensor_t* s) =
            \forall integer i; ( 0 <= i < 200  )  ==> 
                \at(Storage(s)[i], A) == \at(Storage(s)[i], B);
*/

/*@
// tests if every cell of the array is unchanged except the 1 that was popped (future == 0)
predicate
    popIndex{A,B}(sensor_t* s, integer poppedIndex) =
        (
            \forall integer i; ( 0 <= i < 200 && i != poppedIndex )  ==> 
                \at(Storage(s)[i], A) == \at(Storage(s)[i], B)
        )
            &&
        \at(Storage(s)[poppedIndex], B) == 0;
*/

/*@
// tests if there are no cells with the same ID
predicate
    NoIdEqual{L}(sensor_t* s) =
        \forall integer i ; 0 <= i < 200 && 

            \forall integer k ; 0 <= k < 200 &&

                k != i ==> \valid(Storage(s)[i]) && 
                \valid(Storage(s)[k]) &&
                 Storage(s)[i]->id != Storage(s)[k]->id ;
*/

/*@
predicate Valid{L}(sensor_t* s) =  \valid(s) &&
                                0 < Capacity &&
                                0 <= Size(s) < Capacity &&
                \valid(Storage(s) + (0..Capacity-1));
*/

/*@
    predicate ValidSize(sensor_t *s) = Size(s) <= Capacity;
    predicate ExistsFreeSlot{L}(sensor_t *s) = Size(s) < Capacity ==> (\exists integer k ; 0 <= k < Capacity && Storage(s)[k] == \null);
*/

/*@
    type invariant valid_size(sensor_t *s) = ValidSize(s);
    type invariant free_slot(sensor_t *s) = ExistsFreeSlot(s);
*/

void init_sensor(sensor_t *sensor);

int add_result(sensor_t *sensor, scan_result_t *result);
int get_result(sensor_t *sensor, int id, scan_result_t **results, REQUEST_TYPE rtype);

/* ******************* */

#define RESPONSE int
#define OK 0
#define ERROR_SCAN_A 1
#define ERROR_GET_SCAN_A 2

RESPONSE SENSOR_A_request_x (const SENSOR_request_scan_x_t *params_p, int *id_p);
RESPONSE SENSOR_A_get_result_scan_x (int id, SENSOR_A_get_result_x_t *params_p);

RESPONSE SENSOR_A_request_y(const SENSOR_request_scan_y_t *params_p, int *id_p);
RESPONSE SENSOR_A_get_result_scan_y(int id, SENSOR_A_get_result_y_t *params_p);



/* global queue instance to be modified by the assignment functions */

sensor_t *sensor_result_queue;


#endif