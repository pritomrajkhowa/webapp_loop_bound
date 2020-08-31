import FOLTranslation as folTras


def postProcessHandleOutPut(insts_list):


    inst_stack =[]

    for inst in insts_list:
        
        inst_stack.append(inst)

    program = None

    while inst_stack:

        inst = inst_stack.pop()

        if program is None:

           if inst[0]=='block':

              temp_program = processBlock(inst[1])     

              if temp_program is not None:     

                 program = temp_program

           elif inst[0]=='loop':

              temp_program = processLoop(inst[1])     

              if temp_program is not None:     

                 program = temp_program



           else:
             
              program = inst

        else:

           if inst[0]=='block':

              temp_program = processBlock(inst[1])     

              if temp_program is not None:     

                 program = ['-1', 'seq', temp_program, program]


           elif inst[0]=='loop':


              temp_program = processLoop(inst[1])     

              if temp_program is not None:     

                 program =  ['-1', 'seq', temp_program, program]

              else:


                 temp_program = contructLoopWithMultCond(inst[1])

                 if temp_program is not None:     

                    program =  ['-1', 'seq', temp_program, program]



         
           else:

               temp_program = ['-1', 'seq', inst]

               temp_program.append(program)

               program = temp_program


    return program





def processBlock(insts_list):


    if len(insts_list)==1:

       if insts_list[0][0]=='loop':

          return processLoop(insts_list[0][1])

       else:
          
          return insts_list[0]

    else:

       return constructIfBlock(insts_list)




def constructIfBlock(insts_list):


    pre_insturct_list = []

    post_insturct_list = []

    condition_list = []

    pre_insturct = None

    post_insturct = None

    if_stmt= None

    if_else_stmt= None


    condition = None

    for inst in insts_list:


        if inst[0]=='br_if' and inst[-1]=='0':

           condition = inst[1][2]

           condition_list.append(condition)

           pre_insturct_list.append(pre_insturct)

           if post_insturct is not None:

              post_insturct_list.append(post_insturct)

           post_insturct=[]

        elif inst[0]=='br' and inst[-1]==0:

             print('XXX')

        elif inst[0]=='br' and inst[-1]==1:

             if_stmt = post_insturct

             if_else_stmt = []


        elif post_insturct is None:

           if pre_insturct is None:

              pre_insturct=[]

           if inst[0]=='block':

              temp_program = processBlock(inst[1])     

              #if temp_temp_program is not None:     

              #   temp_program = ['-1', 'seq', temp_temp_program, temp_program]

              pre_insturct.append(temp_program)

           else:

              pre_insturct.append(inst)

        else:

           if if_else_stmt is not None:

              if_else_stmt.append(inst)

           else:

               post_insturct.append(inst)

    if if_stmt is not None and if_else_stmt is not None and len(if_else_stmt)>0:

        seq_if_stmt = postProcessHandleOutPut(if_stmt)

        seq_if_else_stmt = postProcessHandleOutPut(if_else_stmt)

        return ['-1','if2', condition, seq_if_stmt, seq_if_else_stmt]


    elif post_insturct is not None:

         post_insturct_list.append(post_insturct)

    elif len(post_insturct_list)==0:

         program = postProcessHandleOutPut(pre_insturct)

         return program



    program = None

    for x in range(0,len(condition_list)):

        pre_insturct = pre_insturct_list[x]

        post_insturct = post_insturct_list[x]

        condition = condition_list[x]

        if post_insturct is not None and pre_insturct is not None:

              if len(pre_insturct)>0:

                 seq_pre_insturct = postProcessHandleOutPut(pre_insturct)

                 seq_post_insturct = postProcessHandleOutPut(post_insturct)

                 if program is None:

                    program = ['-1', 'seq', seq_pre_insturct ,['-1','if1', condition, seq_post_insturct]]

                 else:

                    program = ['-1', 'seq', program, ['-1', 'seq', seq_pre_insturct ,['-1','if1', condition, seq_post_insturct]]]


              else:

                 seq_post_insturct = postProcessHandleOutPut(post_insturct)

                 if program is None:

                    program = ['-1','if1', condition, seq_post_insturct]

                 else:

                    program = ['-1', 'seq', program, ['-1','if1', condition, seq_post_insturct]]


        elif post_insturct is not None and pre_insturct is None:

              seq_post_insturct = postProcessHandleOutPut(post_insturct)

              if program is None:

                    program = ['-1','if1', condition, seq_post_insturct]

              else:
                    #if program[1]=='if1':

                    #   new_body=['-1', 'seq', program[-1],['-1','if1', condition, seq_post_insturct]]

                    #else:

                    program = ['-1', 'seq', program, ['-1','if1', condition, seq_post_insturct]]



    return program




def processLoop(insts_list):

    pre_insturct = None

    post_insturct = None

    condition = None

    for inst in insts_list:

        #print(inst)

        if inst[0]=='br_if' and inst[-1]=='1':

           condition = inst[1][2]

           post_insturct=[]

        elif inst[0]=='br' and inst[-1]==0:


           if post_insturct is not None and pre_insturct is not None:

              seq_pre_insturct = postProcessHandleOutPut(pre_insturct)

              seq_post_insturct = postProcessHandleOutPut(post_insturct)


              return ['-1', 'seq', seq_pre_insturct, ['-1','while', condition, ['-1', 'seq', seq_pre_insturct, seq_post_insturct]]]


        elif post_insturct is None:

           if pre_insturct is None:

              pre_insturct=[]

           pre_insturct.append(inst)

        else:

           post_insturct.append(inst)

    return None

       

def contructLoopWithMultCond(insts_list):    

    list_stmt = [] 

    for inst in insts_list: 

        #print(inst)

        if inst[0]=='block':

           temp_list_stmt = blockToStmt(inst[1]) 

           for temp_inst in temp_list_stmt:   

               list_stmt.append(temp_inst)

        else:

           list_stmt.append(inst)

    #print('+++++++++++++++++++++++++++++++')

    #for inst in list_stmt: 

    #    print(inst)

    #print('+++++++++++++++++++++++++++++++')

    program = 	None

    condition_map = {}

    program_map = {}




    for inst in list_stmt:

        if program is None:


           if inst[0]=='br_if' and inst[-1]=='0':

              program_map[folTras.expr2string1(inst[1][-1])] = program

              condition_map[folTras.expr2string1(inst[1][-1])] = inst[1]

              program = None


           elif inst[0]=='br' and inst[-1]==1:

                condition = None

                temp_program = None

                for X in condition_map:

                    if condition is None:

                       condition = condition_map[X][-1]

                       temp_program = program_map[X]


                    else:

                       condition = ['&',condition_map[X][-1],condition]

                       temp_program = ['-1', 'seq', temp_program, program_map[X]]

                if condition is not None and program is not None:

                   return ['-1', 'seq', temp_program, ['-1', 'while', condition, ['-1', 'seq', program, temp_program]]]


           elif inst[0]=='block':

              temp_program = processBlock(inst[1])     

              if temp_program is not None:     

                 program = temp_program

           elif inst[0]=='loop':

              temp_program = processLoop(inst[1])     

              if temp_program is not None:     

                 program = temp_program

           else:
             
              program = inst

        else:

           if inst[0]=='br_if' and inst[-1]=='0':

              program_map[folTras.expr2string1(inst[1][-1])] = program

              condition_map[folTras.expr2string1(inst[1][-1])] = inst[1] 



              program = None


           elif inst[0]=='br' and inst[-1]==1:

                condition = None

                temp_program = None

                for X in condition_map:

                    if condition is None:

                       condition = condition_map[X][-1]

                       temp_program = program_map[X]


                    else:

                       condition = ['&',condition_map[X][-1],condition]

                       temp_program = ['-1', 'seq', temp_program, program_map[X]]

                if condition is not None and program is not None:


                   return ['-1', 'seq', temp_program, ['-1', 'while', condition, ['-1', 'seq', program, temp_program]]]


           elif inst[0]=='block':

              temp_program = processBlock(inst[1])   

              if temp_program is not None:     

                 program = ['-1', 'seq', temp_program, program]


           elif inst[0]=='loop':


              temp_program = processLoop(inst[1])     

              if temp_program is not None:     

                 program =  ['-1', 'seq', temp_program, program]

              else:

                 temp_program = contructLoopWithMultCond(inst[1])

                 if temp_program is not None:     

                    program =  ['-1', 'seq', program, temp_program]

           else:

               temp_program = ['-1', 'seq']

               temp_program.append(program)

               temp_program.append(inst)

               program = temp_program

    if len(condition_map)==0:
       #Body with If Else and Break
       program = None

       condition = None

       post_condition_stmt = None

       for inst in list_stmt:

           if program is None:

              if inst[0]=='block':

                 temp_program = processBlock(inst[1])     

                 if temp_program is not None:     

                    program = temp_program

              elif inst[0]=='loop':

                 temp_program = processLoop(inst[1])     

                 if temp_program is not None:     

                    program = temp_program

              else:
             
                 program = inst

           else:


              if inst[0]=='block':

                 temp_program = processBlock(inst[1])   

                 if temp_program is not None:  

                    if temp_program[-1] is None:
                       print('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5')
                       print(program)
                       print('---------------------------------')
                       print(temp_program)
                       print('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5') 

                    program = ['-1', 'seq', temp_program, program]


              elif inst[0]=='loop':

                  temp_program = processLoop(inst[1])     

                  if temp_program is not None:     

                     program =  ['-1', 'seq', temp_program, program]

                  else:

                     temp_program = contructLoopWithMultCond(inst[1])

                     if temp_program is not None:     

                        program =  ['-1', 'seq', program, temp_program]

              else:

                  temp_program = ['-1', 'seq']

                  temp_program.append(program)

                  temp_program.append(inst)

                  program = temp_program








def blockToStmt(insts_list):

    list_stmt = [] 

    for inst in insts_list:     

       list_stmt.append(inst)

    return list_stmt




