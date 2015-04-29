#include "sensor.h"

#include <stdlib.h>

/* global queue instance to be modified by the assignment functions */

extern sensor_t *sensor_result_queue;

/*
Pre:
Capacity > 0

*/

/*@
    requires \valid(s);
    requires \valid(Storage(s)+(0..Capacity−1));

    requires Capacity > 0;

    assigns Storage(s)[0..(Capacity−1)];
    assigns s->size;

    ensures EMPTY: Empty(s);

    ensures NULLIFIED: \forall integer k ; (0 <= k < Capacity) ==> (Storage(s)[k] == \null);
    ensures VALID: \valid(s) &&
                                0 < Capacity &&
                                0 <= Size(s) < Capacity &&
                \valid(Storage(s) + (0..Capacity-1));
*/

void init_sensor(sensor_t *s)
{
    int i;
    /*@
        loop invariant RANGE: 0 <= i <= Capacity;
        loop invariant ZERO: \forall integer k; 0 <= k < i ==> (Storage(s)[k] == \null);
        loop assigns i, Storage(s)[0..(Capacity−1)];

        loop variant Capacity - i;
    */
    for(i = 0; i < CAPACITY; i++)
        s->scan_results[i] = 0;

    s->size = 0;
}

/*@
    requires Valid(s);
    requires \valid(result);

    requires ExistsFreeSlot(s);

    behavior full:
        assumes Size(s) >= Capacity;

        assigns \nothing;
        ensures \at(Size(s), Pre) == \at(Size(s), Here);

        ensures \result == -1;

    behavior dup_ids:
        assumes Size(s) < Capacity;
        assumes \exists integer k ; 0 <= k < Capacity && Storage(s)[k] == \null;
        assumes \exists integer k ; 0 <= k < Capacity && Storage(s)[k] != \null && Storage(s)[k]->id == result->id;

        ensures RESULT_IS_2: \result == -2;
        ensures Valid(s);

    behavior success:
        assumes Size(s) < Capacity;
        assumes \exists integer k ; 0 <= k < Capacity && Storage(s)[k] == \null;
        assumes \forall integer k ; 0 <= k < Capacity && Storage(s)[k] != \null ==> Storage(s)[k]->id != result->id;

        ensures RESULT_ADDED: \exists integer k ; 0 <= k < Capacity && \at(Storage(s)[k], Pre) == 0 && \at(Storage(s)[k], Here) == result;
        ensures SIZE_INCREMENT: \at(s->size, Here) == \at(s->size, Pre) + 1;

        ensures RESULT_IS_ZERO: \result == 0;
        ensures Valid(s);

    complete behaviors;
    disjoint behaviors;
*/

int add_result(sensor_t *s, scan_result_t *result)
{
    if(s->size >= CAPACITY)
        return -1;

    int slot = -1;

    /*@
        loop invariant RANGE:         0 <= i <= Capacity;
        // loop invariant NOT_FOUND:    \forall integer k ; 0 <= k < i ==> Storage(s)[k] != \null;
        // loop invariant NO_SLOT:        slot == \null;
        loop invariant NO_DUP_IDS:    \forall integer k ; 0 <= k < i ==> ( Storage(s)[k] != \null ==> Storage(s)[k]->id != result->id );
        loop invariant FOUND_SLOT:    (\exists integer k ; 0 <= k < i && Storage(s)[k] == \null) ==> slot >= 0 && slot < i && Storage(s)[slot] == \null;
        loop invariant VALID_SLOT:     slot < Capacity;
        loop assigns i, slot;
        loop variant Capacity - i;
    */

    for(int i = 0; i < CAPACITY; i++)
    {
        if(s->scan_results[i] == 0)
        {
            slot = i;
        }
        else if(s->scan_results[i]->id == result->id)
        {
            return -2;
        }
    }

    // assert EXISTS_SLOT: (\exists integer k ; 0 <= k < Capacity && Storage(s)[k] == 0) ==> (slot != -1);
    // assert NO_DUPS: \forall integer k ; 0 <= k < Capacity && Storage(s)[k] != \null ==> Storage(s)[k]->id != result->id;

    // assert SLOT_VALID: slot >= 0 && slot < Capacity;
    s->scan_results[slot] = result;
    // assert RESULT_IS_IN: Storage(s)[slot] == result;
    s->size++;

    return 0;
}

/*@
    requires Valid(s);

    requires \valid(results);

    requires NoIdEqual{Here}(s); 

    behavior no_result:
        assumes  \forall integer k; (0 <= k < 200) ==> !(\valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype));
        ensures NRES : \result == -1;

        ensures Unchanged{Pre,Here}(s);

        ensures Valid(s);
        
    behavior has_result:
        assumes  \exists integer k; (0 <= k < Capacity) && \valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype);
        ensures HRES : \result == 0;

        ensures \exists integer k; (0 <= k < Capacity) && \valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype)
             && popIndex{Pre,Here}(s, k);

        ensures Valid(s);


    complete behaviors;
    disjoint behaviors;

*/
int get_result(sensor_t *s, int id, scan_result_t **results, REQUEST_TYPE rtype)
{

    /*@
        loop invariant RANGE: 0 <= i <= Capacity;
        loop invariant \forall integer k; (0 <= k < i) ==> !(\valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype));
        loop assigns i;
        loop variant Capacity - i;
    */
    for(int i = 0; i < CAPACITY; i++)
    {
        if( s->scan_results[i]  && 
            s->scan_results[i]->id == id &&
            s->scan_results[i]->request_type == rtype
          )
        {
            *results = s->scan_results[i];
            s->scan_results[i] = 0;
            s->size--;
            return 0;
        }
    }

    return -1;
}


// ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==
//   ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==
// ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==  ==
/*

Can you check the property that if we request more than 200 scans that the function will return ERROR_SCAN_A or ERROR_SCAN_B;
Can you also check that if during a get_result someone passes an invalid Id that the returned error code is ERROR_GET_SCAN_A or ERROR_GET_SCAN_B;
The previous functions should also return to clients the id of the scan in the pointer id_p (I do not see this happening now). In the case of an error the pointer should be -1; Also a property to check;
Please use the #defines OK, Error, etc.

#define RESPONSE int
#define OK 0
#define ERROR_SCAN_A 1
#define ERROR_GET_SCAN_A 2

*/

/*@
    requires Valid(sensor_result_queue);
    requires \valid(params_p);
    requires \valid(id_p);

    behavior not_full:
        assumes NotFull(sensor_result_queue);

        ensures RESULT_IS_OK:\result == 0;
        ensures Valid(sensor_result_queue);

    behavior full:
        assumes Full(sensor_result_queue);

        ensures RESULT_IS_BAD: \result == 1;
        ensures Valid(sensor_result_queue);


    complete behaviors;
    disjoint behaviors;
*/

RESPONSE SENSOR_A_request_x (const SENSOR_request_scan_x_t *params_p, int *id_p)
{
    /* Check for free space Example: request_cout < 200 */

    if(sensor_result_queue->size >= CAPACITY)
    {
        return ERROR_GET_SCAN_A;
    }

    /*
        Do something with params_p
    */

    SENSOR_A_get_result_x_t *scan_result_x = (SENSOR_A_get_result_x_t *) malloc (sizeof (SENSOR_A_get_result_x_t));

    scan_result_x->value1 = /* ... */ 0.0f;
    scan_result_x->value2 = /* ... */ 0.0f;

    scan_result_t *scan_result = (scan_result_t *) malloc (sizeof (scan_result_t));

    scan_result->id = 0 /* Should be generated */;
    // *id_p = 0

    /* Tag it as a X result */
    scan_result->request_type = REQUEST_X;

    /* Assign nested structure */
    scan_result->result_x = scan_result_x;

    /* Push result onto the global queue */

    int res = add_result(sensor_result_queue, scan_result);
    
    if(res < 0)
        return ERROR_GET_SCAN_A;
    else
        return OK;
}

/*
#define REQUEST_TYPE int
#define REQUEST_X 0
#define REQUEST_Y 1
*/

/*@
    requires Valid(sensor_result_queue);
    requires \valid(params_p);

    behavior valid_id:
        assumes \exists integer k; (0 <= k < Capacity) && Storage(sensor_result_queue)[k]->id == id && (Storage(sensor_result_queue)[k]->request_type == 0);
        assigns *params_p;

        ensures \result == 0;
        ensures Valid(sensor_result_queue);

    behavior invalid_id:
        assumes \forall integer k; (0 <= k < Capacity) ==> Storage(sensor_result_queue)[k]->id != id || (Storage(sensor_result_queue)[k]->request_type != 0);
        ensures \result == 2;
        ensures Valid(sensor_result_queue);

    complete behaviors;
    disjoint behaviors;
*/
RESPONSE SENSOR_A_get_result_scan_x (int id, SENSOR_A_get_result_x_t *params_p)
{
    scan_result_t *scan_result_temp;

    int res = get_result(sensor_result_queue, id, &scan_result_temp, REQUEST_X);

    if(res < 0)
        return ERROR_GET_SCAN_A;

    *params_p = *(scan_result_temp->result_x);

    return OK;
}

/*@
    requires Valid(sensor_result_queue);
    requires \valid(params_p);
    requires \valid(id_p);

    behavior not_full:
        assumes NotFull(sensor_result_queue);

        ensures RESULT_IS_OK:\result == 0;
        ensures Valid(sensor_result_queue);

    behavior full:
        assumes Full(sensor_result_queue);

        ensures RESULT_IS_BAD: \result == 1;
        ensures Valid(sensor_result_queue);

    complete behaviors;
    disjoint behaviors;
*/
RESPONSE SENSOR_A_request_y(const SENSOR_request_scan_y_t *params_p, int *id_p)
{
    /* Check for free space: request_cout < 200 */

    if(sensor_result_queue->size >= CAPACITY)
    {
        return ERROR_GET_SCAN_A;
    }

    /*
        Do something with params_p
    */

    SENSOR_A_get_result_y_t *scan_result_y = (SENSOR_A_get_result_y_t *) malloc (sizeof (SENSOR_A_get_result_y_t));

    scan_result_y->value1 = /* ... */ 0.0f;
    scan_result_y->value2 = /* ... */ 0.0f;
    scan_result_y->value3 = /* ... */ 0.0f;

    scan_result_t *scan_result = (scan_result_t *) malloc (sizeof (scan_result_t));

    scan_result->id = 0 /* Should be generated */;
    // *id_p = 0

    /* Tag it as a Y result */
    scan_result->request_type = REQUEST_Y;

    /* Assign nested structure */
    scan_result->result_y = scan_result_y;

    /* Push result onto the global queue */
    int res = add_result(sensor_result_queue, scan_result);

    if(res < 0)
        return ERROR_GET_SCAN_A;

    return OK;
}


/*@
    requires Valid(sensor_result_queue);
    requires \valid(params_p);

    behavior valid_id:
        assumes \exists integer k; (0 <= k < Capacity) && Storage(sensor_result_queue)[k]->id == id 
        && (Storage(sensor_result_queue)[k]->request_type == 1);
        assigns *params_p;

        ensures \result == 0;
        ensures Valid(sensor_result_queue);

    behavior invalid_id:
        assumes \forall integer k; (0 <= k < Capacity) ==> Storage(sensor_result_queue)[k]->id != id || 
        (Storage(sensor_result_queue)[k]->request_type != 1);
        
        ensures \result == 2;
        ensures Valid(sensor_result_queue);

    complete behaviors;
    disjoint behaviors;
*/
RESPONSE SENSOR_A_get_result_scan_y(int id, SENSOR_A_get_result_y_t *params_p)
{
    scan_result_t *scan_result_temp;

    int res = get_result(sensor_result_queue, id, &scan_result_temp, REQUEST_Y);

    if(res < 0)
        return ERROR_SCAN_A;

    *(params_p) = *(scan_result_temp->result_y);

    return OK;
}
