//
// Created by nikhil on 12/11/2019.
//

#ifndef TRIDENT_RUNTIME_H
#define TRIDENT_RUNTIME_H


#define TRIDENT_OUTPUT(id, typestr, value) \
  __trident_output(id, typestr, value);


int __trident_choice(char* lid, char* typestr,
                    int** rvals, char** rvals_ids, int rvals_size,
                    int** lvals, char** lvals_ids, int lvals_size);
int __trident_choice_semfix(char* lid, char* typestr,
                     int** rvals, char** rvals_ids, int rvals_size,
                     int** lvals, char** lvals_ids, int lvals_size);

int __trident_output(char* id, char* typestr, int value);


#endif //TRIDENT_RUNTIME_H
