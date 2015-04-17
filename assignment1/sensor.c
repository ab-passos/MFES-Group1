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

    ensures VALID: Valid(s);
    ensures EMPTY: Empty(s);

    ensures NULLIFIED: \forall integer k ; (0 <= k < Capacity) ==> (Storage(s)[k] == \null);
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
/*
Pre:
Size < Capacity
valid sensor
valid result
valid id

Post:
sensor->indexes->size = \old(sensor->indexes->size) - 1
id = \old(sensor->indexes->top)
sensor->array [id] = result
\forall integer i; i != id ==> \at(sensor->scan_results[i], Pre) ==  \at(sensor->scan_results[i], Here)
*/

/*
    id must be a valid int*

    two behaviours
        if no "holes" in array insert in next open position;
    else
        insert into first "hole"
*/

/*@
    requires \valid(s);
    requires \valid(result);

    requires \valid(Storage(s)+(0..Capacity−1));

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

        ensures RESULT_IS_BAD_2: \result == -2;

    behavior success:
        assumes Size(s) < Capacity;
        assumes \exists integer k ; 0 <= k < Capacity && Storage(s)[k] == \null;
        assumes \forall integer k ; 0 <= k < Capacity && Storage(s)[k] != \null ==> Storage(s)[k]->id != result->id;

        ensures RESULT_ADDED: \exists integer k ; 0 <= k < Capacity && \at(Storage(s)[k], Pre) == 0 && \at(Storage(s)[k], Here) == result;
        ensures SIZE_INCREMENT: \at(s->size, Here) == \at(s->size, Pre) + 1;
        ensures RESULT_IS_ZERO: \result == 0;
    
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
    requires \valid(s);
    requires \valid(Storage(s)[0..(Capacity−1)]);
    requires s->size > 0;

    requires \valid(results);

    requires NoIdEqual(s); 

    behavior no_result:
        assumes  \forall integer k; (0 <= k < 200) ==> !(\valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype));
        ensures NRES : \result == -1;
        ensures NoIdEqual(s); 
        ensures Unchanged{Pre,Here}(s);
        
    behavior has_result:
        assumes  \exists integer k; (0 <= k < Capacity) && \valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype);
        ensures HRES : \result == 0;
        ensures NoIdEqual(s);
        ensures \exists integer k; (0 <= k < Capacity) && \valid(Storage(s)[k]) && Storage(s)[k]->id == id && (Storage(s)[k]->request_type == rtype)
             && popIndex{Pre,Here}(s, k);


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



/*@

    ensures \result == 0 || \result == 1;
*/
RESPONSE SENSOR_A_request_x (const SENSOR_request_scan_x_t *params_p, int *id_p)
{
    /* Check for free space Example: request_cout < 200 */

    if(sensor_result_queue->size >= CAPACITY)
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

    scan_result->id = 000000000000001;

    /* Tag it as a X result */
    scan_result->request_type = REQUEST_X;

    /* Assign nested structure */
    scan_result->result_x = scan_result_x;

    /* Push result onto the global queue */


    int res = add_result(sensor_result_queue, scan_result);
    
    if(res != 0)
        return ERROR_SCAN_A;


    return OK;
}


/*@

    ensures \result == 0 || \result == 2;
*/
RESPONSE SENSOR_A_get_result_scan_x (int id, SENSOR_A_get_result_x_t *params_p)
{
    scan_result_t *scan_result_temp;

    int res = get_result(sensor_result_queue, id, &scan_result_temp, REQUEST_X);

    if(res != 0)
        return ERROR_GET_SCAN_A;

    *params_p = *(scan_result_temp->result_x);

    return OK;
}




/*@

    ensures \result == 0 || \result == 1;
*/
RESPONSE SENSOR_A_request_y(const SENSOR_request_scan_y_t *params_p, int *id_p)
{
    /* Check for free space: request_cout < 200 */

    if(sensor_result_queue->size >= CAPACITY)
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

    scan_result->id = 0000000000000000000000000000000000000000000000000000000000001;
    /* Tag it as a Y result */
    scan_result->request_type = REQUEST_Y;

    /* Assign nested structure */
    scan_result->result_y = scan_result_y;

    /* Push result onto the global queue */
    int res = add_result(sensor_result_queue, scan_result);

    if(res != 0)
        return ERROR_SCAN_A;

    return OK;
}


/*@
    ensures \result == 0 || \result == 2;
*/
RESPONSE SENSOR_A_get_result_scan_y(int id, SENSOR_A_get_result_y_t *params_p)
{
    scan_result_t *scan_result_temp = NULL;

    int res = get_result(sensor_result_queue, id, &scan_result_temp, REQUEST_Y);

    if(res != 0)
        return ERROR_SCAN_A;

    *(params_p) = *(scan_result_temp->result_y);

    return OK;
}
