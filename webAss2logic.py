#import commandclass
import subprocess, threading
import sys
import os
import wadze
import all_classes as allclass
import FOLTranslation as folTras
import constructIntmate as consInt
currentdirectory = os.path.dirname(os.path.realpath(__file__))



Count_Assertion=1

Count_Assumption=1



def displayOutput(insts_list):
    print('==================')
    for inst in insts_list:

        if isinstance(inst, list):

 
           displayOutput(inst)

        else:
    
           print(inst)
    print('==================')



def tempdisplayOutput(insts_list):

    for inst in insts_list:

        if inst[0]=='block':

           print('%%%%%%%%%%%%%%1')

           tempdisplayOutput(inst[1])

           print('%%%%%%%%%%%%%%2')


        elif inst[0]=='loop':
 
           print('@@@@@@@@@@@@@@')

           tempdisplayOutput(inst[1])

           print('@@@@@@@@@@@@@@')

        else:

           print(inst)







def blockHandler(codelist, global_stack,local_stack):

    global Count_Assertion

    global Count_Assumption

    insts_list = []


    for inst in codelist:

        #print(inst)

        #print('=============1')

        if len(inst)==1:

           if inst[0] =='i32.sub':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['-', temp2, temp1])

           elif inst[0] =='i32.add':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['+', temp2, temp1])


           elif inst[0] =='i32.mul':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['*', temp2, temp1])

           elif inst[0] =='i32.and':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['&', temp2, temp1])

           elif inst[0] =='i32.or':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['|', temp2, temp1])


           elif inst[0] =='i32.div_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['/', temp2, temp1])


           elif inst[0] =='i32.div_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['/', temp2, temp1])


           elif inst[0] == 'i32.gt_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['>', temp2, temp1])

           elif inst[0] == 'i32.lt_s' or inst[0] == 'i32.lt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['<', temp2, temp1])


           elif inst[0] == 'i32.ge_s' or inst[0] == 'i32.ge_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['>=', temp2, temp1])


           elif inst[0] == 'i32.le_s' or inst[0] == 'i32.le_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['<=', temp2, temp1])


           elif inst[0] =='i64.sub' :

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['-', temp2, temp1])


           elif inst[0] =='i64.add':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['+', temp2, temp1])

           elif inst[0] =='i64.mul':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['*', temp2, temp1])


           elif inst[0] =='i64.and':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['&', temp2, temp1])


           elif inst[0] =='i64.or':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['|', temp2, temp1])

           elif inst[0] =='i64.div_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['/', temp2, temp1])


           elif inst[0] =='i64.div_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['/', temp2, temp1])

           elif inst[0] == 'i64.gt_s' or inst[0] == 'i64.gt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['>', temp2, temp1])


           elif inst[0] == 'i64.lt_s' or inst[0] == 'i64.lt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['<', temp2, temp1])


           elif inst[0] == 'i64.ge_s' or inst[0] == 'i64.ge_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['>=', temp2, temp1])

           elif inst[0] == 'i64.le_s' or inst[0] == 'i64.le_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append(['<=', temp2, temp1])



           elif inst[0] =='i64.extend_i32_s':

              temp = local_stack.pop()

              local_stack.append(['extend32to64fun', temp])

           elif inst[0] == 'f64.convert_i64_s':

              temp = local_stack.pop()

              local_stack.append(['converti64tof64fun', temp])

           elif inst[0] == 'return':

              if len(local_stack)>0:

                 temp = local_stack.pop()

                 insts_list.append(['-1','=',['ret'],temp])


           elif inst[0] == 'i32.eq':
       
             temp1 = local_stack.pop()

             temp2 = local_stack.pop()

             local_stack.append(['==', temp1,temp2])


           elif inst[0] == 'i32.ne':
       
             temp1 = local_stack.pop()

             temp2 = local_stack.pop()

             local_stack.append(['!=', temp1,temp2])




           elif inst[0] == 'i32.eqz':
       
             temp = local_stack.pop()

             local_stack.append(['==', temp,['0']])


        elif len(inst)==2:

          inst_type, inst_operant = inst

          if inst_type=='call':

             if inst_operant==4:

                var_name = '__VERIFIER_nondet_int'
                
                local_stack.append([var_name])

             elif inst_operant==5:

                var_name = 'abort'
                
                local_stack.append([var_name])


             elif inst_operant==2:

                Count_Assumption = Count_Assumption + 1

                temp = local_stack.pop()

                insts_list.append(['-1','=',['_'+str(Count_Assumption)+'_assumption'], temp])


             elif inst_operant==3:

                temp = local_stack.pop()

                Count_Assertion = Count_Assertion+1

                insts_list.append(['-1','=',['_'+str(Count_Assertion)+'_assertion'],temp])

          elif inst_type=='br':

              insts_list.append(['br', inst_operant])

          elif inst_type=='br_if':

             temp = local_stack.pop()

             insts_list.append(['br_if',['-1','if',['==', temp, ['0']]],str(inst_operant)])

          elif inst_type=='global.get':

             var_name='v'+str(inst_operant)+'g'

             local_stack.append([var_name])

          elif inst_type=='global.set':

             temp = local_stack.pop()

             var_name='v'+str(inst_operant)+'g'

             insts_list.append(['-1','=',[var_name], temp])

          elif inst_type=='local.get':

             var_name='v'+str(inst_operant)+'l'

             local_stack.append([var_name])

          elif inst_type=='local.set':

             temp = local_stack.pop()

             var_name='v'+str(inst_operant)+'l'

             insts_list.append(['-1','=',[var_name], temp])

          elif inst_type=='i32.const':

              local_stack.append([str(inst_operant)])

          elif inst_type=='i64.const':

              local_stack.append([str(inst_operant)])



        elif len(inst)==3:

          inst_type, inst_operant1, inst_operant2 = inst

          if inst_type =='block':

             temp_insts_list = blockHandler(inst_operant2, global_stack,local_stack)

             insts_list.append(['block', temp_insts_list])
                                    

          elif inst_type =='loop':

             temp_insts_list = blockHandler(inst_operant2, global_stack,local_stack)

             insts_list.append(['loop', temp_insts_list])
                  

          elif inst_type =='i32.store':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()


              insts_list.append(['-1','=',['memory'+str(inst_operant1)+'op32off',['+', temp2,[str(inst_operant2)]]], temp1])



          elif inst_type =='i64.store':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()


              insts_list.append(['-1','=',['memory'+str(inst_operant1)+'op64off',['+', temp2,[str(inst_operant2)]]], temp1])


          elif inst_type =='i32.load':


              temp = local_stack.pop()

              
              local_stack.append(['memory'+str(inst_operant1)+'op32off',['+', temp,[str(inst_operant2)]]])


          elif inst[0] =='i64.load':


              temp = local_stack.pop()
              

              local_stack.append(['memory'+str(inst_operant1)+'op32off',['+', temp, [str(inst_operant2)]]])


          else:

              print('========================')

              print(inst_type)

              print(inst_operant1)

              print(inst_operant2)

              print('========================')

        else:

          inst_type = inst           
          print('========================')
          print(inst_type)
          print('========================')


    return insts_list









def translation():

    global Count_Assertion

    global Count_Assumption


    if (os.path.exists(currentdirectory+'/test.wasm')): 
       with open('test.wasm', 'rb') as file:
            data = file.read()
       module = wadze.parse_module(data)

       # If you also want function code decoded into instructions, do this
       module['code'] = [ wadze.parse_code(c) for c in module['code']]

       global_stack = [] 

       list_fun_para =[]

       list_fun_ret = []

       list_fun_obj = []

       list_table_obj = []

       list_global_obj = []

       list_memory_obj = []

       export_map_memory = {}

       export_map_function = {}

       export_map_global = {}



       for x in module['type']:
                  
           list_fun_para.append(x[0])

           list_fun_ret.append(x[1])

       for x in module['func']:

           funcObj = allclass.functionclass(x, list_fun_para[x], list_fun_ret[x])

           list_fun_obj.append(funcObj)

       for x in module['table']:

           tableObj = allclass.tableclass(x[0],x[1])

           list_table_obj.append(tableObj)


       global_counter=0

       for x in module['global']:

           
           globalObj = allclass.globalclass('v'+str(global_counter)+'g', x[0][0], x[0][1], x[1])

           global_counter = global_counter+1

           list_global_obj.append(globalObj)


       list_memory_obj = module['memory']

       for x in module['export']:

           if isinstance(x, wadze.ExportGlobal):

              export_map_global[x[1]] = x[0]


           if isinstance(x, wadze.ExportFunction):

              export_map_function[x[1]] = x[0]
       

           if isinstance(x, wadze.ExportMemory):

              export_map_memory[x[1]] = x[0]


       exportMapObj = allclass.exportMapclass(export_map_memory, export_map_function, export_map_global)


       fun_list = []       

       vfact_map = {}

       fun_count = 0
       
       
       for exp in module['code']:

           fun_count = fun_count + 1

           #print(exp)

           #if(fun_count==len(list_fun_obj)-1):
           if(fun_count==6):

                local_stack = []

                insts_list = []

                varcount = 1 #Counter for variables 

                var_list = [] #List of all local variable

                for x in exp.locals:
             
                   varcount = varcount+1

                   varObj = allclass.variableclass('v'+str(varcount)+'l',x)

                   var_list.append(varObj)



                insts_list = blockHandler(exp.instructions, global_stack, local_stack)

                #tempdisplayOutput(insts_list)

                program = consInt.postProcessHandleOutPut(insts_list)

                if program is not None:

                   program_fun=[]

                   program_fun.append('-1')

                   program_fun.append('fun')

                   program_fun.append(['function'+str(fun_count)])

                   program_fun.append(program)

                   fun_list.append(program_fun)

                main_program = []

                main_program.append('-1')

                main_program.append('prog')

                main_program.append(fun_list)

                vfact={}

                vfactCount = 0

                for varObj in var_list:

                    vfactCount = vfactCount+1

                    keyvalue = varObj.getVariablename()

                    temp_list = []

                    temp_list.append('_x'+str(vfactCount))

                    temp_list.append('int')

                    vfact[keyvalue] = temp_list


                for varObj in list_global_obj:

                     vfactCount = vfactCount+1

                     keyvalue = varObj.getGlobalname()

                     temp_list = []

                     temp_list.append('_x'+str(vfactCount))

                     temp_list.append('int')

                     vfact[keyvalue] = temp_list

                temp_list1 = []

                vfactCount = vfactCount+1

                temp_list1.append('_x'+str(vfactCount))

                temp_list1.append('int')

                temp_list1.append('int')

                vfact['memory2op32off'] = temp_list1

                temp_list2 = []

                vfactCount = vfactCount+1

                temp_list2.append('_x'+str(vfactCount))

                temp_list2.append('int')

                temp_list2.append('int')

                vfact['memory3op64off'] = temp_list2


                temp_list3 = []

                vfactCount = vfactCount+1

                temp_list3.append('_x'+str(vfactCount))

                temp_list3.append('int')

                vfact['ret'] = temp_list3

                for vcount in range(0,Count_Assertion):

                    temp_list4 = []

                    vfactCount = vfactCount+1

                    temp_list4.append('_x'+str(vfactCount))

                    temp_list4.append('int')

                    vfact['_'+str(vcount+1)+'_assertion'] = temp_list4


                for vcount in range(0,Count_Assumption):


                    temp_list5 = []

                    vfactCount = vfactCount+1

                    temp_list5.append('_x'+str(vfactCount))

                    temp_list5.append('int')

                    vfact['_'+str(vcount+1)+'_assumption'] = temp_list5

                vfact_map['function'+str(fun_count)] = vfact

                return folTras.translate1(main_program,vfact_map,1)





