import dash
import dash_core_components as dcc
import dash_html_components as html
from dash.dependencies import Input, Output, State
import wadze
import subprocess, threading
import sys
import os
import webAss2logic as webasm

currentdirectory = os.path.dirname(os.path.realpath(__file__))


external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']

app = dash.Dash(__name__, external_stylesheets=external_stylesheets)

server = app.server

prev_click=0



def constructText(insts_list,tab):

    output_String = ''

    for inst in insts_list:

        if len(inst)==3:

          inst_type, inst_operant1, inst_operant2 = inst

          if inst_type =='block':

             output_String +=tab+'block\n'

             output_String += constructText(inst_operant2, tab+'\t')+"\n"
                                    

          elif inst_type =='loop':

             output_String +=tab+'loop\n'

             output_String += constructText(inst_operant2, tab+'\t')+"\n"

          else: 
             
             output_String +=tab+str(inst)+'\n'


        else: 
             
             output_String +=tab+str(inst)+'\n'

    return output_String




def translation2wasm(file_name):

    if not(os.path.exists(file_name)): 
       print("File not exits")
       return

    #command1 = currentdirectory+'/wasi-sdk-11.0/bin/clang'+' '+str(file_name)+'  '+'--target=wasm32-unknown-unknown-wasm -nostartfiles -nostdlib -Wl,--no-entry -Wl,--export-all -o test.wasm'
    #command1 = currentdirectory+'/wasi-sdk-11.0/bin/clang'+' '+str(file_name)+'  '+'--target=wasm32-unknown-unknown-wasm -nostartfiles --include-directory=/home/pritom/web_app/MainDevelopment/2/wasi-sdk-11.0/lib/clang/10.0.0/include  -Wl,--no-entry -Wl,--export-all -o test.wasm'
    command1 = currentdirectory+'/wasi-sdk-11.0/bin/clang'+' '+str(file_name)+'  '+'--target=wasm32-unknown-unknown-wasm -nostartfiles -I'+currentdirectory+"/wasi-sdk-11.0/share/wasi-sysroot/include -L"+currentdirectory+'/wasi-sdk-11.0/share/wasi-sysroot/lib/wasm32-wasi -Wl,--no-entry -Wl,--export-all -o test.wasm'
    print(command1)

    try :
       proc = subprocess.Popen(command1, stdout=subprocess.PIPE,shell=True)
       output = proc.stdout.read()
       status=output
    except OSError  as err:
           print('Error Ocurred While executing command')

    if (os.path.exists(currentdirectory+'/test.wasm')): 
       with open('test.wasm', 'rb') as file:
            data = file.read()
       module = wadze.parse_module(data)


       # If you also want function code decoded into instructions, do this
       module['code'] = [ wadze.parse_code(c) for c in module['code']]

       fun_list = []       

       fun_count = 0

       display_webasm_text=''
       
       
       for exp in module['code']:

           display_webasm_text+='\nFunction'+str(fun_count)+"\n"

           fun_count = fun_count + 1

           constructText(exp.instructions,'')

           display_webasm_text+=constructText(exp.instructions,'')

       return display_webasm_text
           



"""
Reading the contain of the file 
"""
def readingFile( filename ):
    content=None
    with open(currentdirectory+"/benchmarks/"+filename) as f:
        content = f.readlines()
    return content

"""
Wrtitting the contain on file 
"""
def writtingFile( filename , content ):
	file = open(currentdirectory+"/"+filename, "w")
	file.write(str(content))
	file.close()


"""
Construct The Program  
"""
def constructProgram( content_values ):
    content=''
    for content_value in content_values:
        content+=content_value
    return content


app.layout = html.Div([
    html.H1(children='Automatic Program Verifier based on First Order Logic and Webassembly'),
    html.H6(children='Designed by Pritom Rajkhowa and Fangzhen Lin'),
    dcc.Dropdown(id='data-dropdown-program', options=[
          {'label':'afnp2014_true-unreach-call-i1.c', 'value':'afnp2014_true-unreach-call-i1.c'},
          {'label':'afnp2014_true-unreach-call-i.c', 'value': 'afnp2014_true-unreach-call-i.c'},
          {'label':'bhmr2007_true-unreach-call-i.c', 'value': 'bhmr2007_true-unreach-call-i.c'},
          {'label':'cggmp2005b_true-unreach-call_true-termination-i.c', 'value':'cggmp2005b_true-unreach-call_true-termination-i.c'},
          {'label':'cggmp2005_true-unreach-call-i.c', 'value': 'cggmp2005_true-unreach-call-i.c'},
          {'label':'css2003_true-unreach-call_true-termination-i.c', 'value': 'css2003_true-unreach-call_true-termination-i.c'},
          {'label':'ddlm2013_true-unreach-call-i.c', 'value': 'ddlm2013_true-unreach-call-i.c'},
          {'label':'gcnr2008_false-unreach-call_false-termination-i.c', 'value': 'gcnr2008_false-unreach-call_false-termination-i.c'},
          {'label':'gj2007b_true-unreach-call_true-termination-i.c', 'value':  'gj2007b_true-unreach-call_true-termination-i.c'},
          {'label':'gj2007_true-unreach-call_true-termination-i.c', 'value': 'gj2007_true-unreach-call_true-termination-i.c'},
          {'label':'gr2006_true-unreach-call_true-termination-i.c', 'value': 'gr2006_true-unreach-call_true-termination-i.c'},
          {'label':'gsv2008_true-unreach-call_true-termination-i.c', 'value': 'gsv2008_true-unreach-call_true-termination-i.c'},
          {'label':'hhk2008_true-unreach-call_true-termination-i.c', 'value': 'hhk2008_true-unreach-call_true-termination-i.c'},
          {'label':'jm2006_true-unreach-call_true-termination-i.c', 'value': 'jm2006_true-unreach-call_true-termination-i.c'},
          {'label':'jm2006_variant_true-unreach-call_true-termination-i.c', 'value':'jm2006_variant_true-unreach-call_true-termination-i.c'},
          {'label':'count_by_1_true-unreach-call_true-termination.c', 'value':'count_by_1_true-unreach-call_true-termination.c'},
          {'label':'count_by_1_variant_true-unreach-call_true-termination.c', 'value':'count_by_1_variant_true-unreach-call_true-termination.c'},
          {'label':'count_by_2_true-unreach-call_true-termination.c', 'value':'count_by_2_true-unreach-call_true-termination.c'}
    ], value='afnp2014_true-unreach-call-i.c'),
      html.H6(children='Input Program'),
      dcc.Textarea(
        id='textarea-input-program1',
        style={'width': '100%', 'height': 200},
    ),
     html.Div([
		html.Button('Verify', id='submit_button'),
      ]),
      html.H6(children='Assembly Program(Text)'),
      dcc.Textarea(
        id='textarea-input-program2',
        style={'width': '100%', 'height': 200},
    ),
      html.H6(children='First Order Logic Axioms'),
      dcc.Textarea(
        id='textarea-input-program3',
        style={'width': '100%', 'height': 200},
    ),



])


@app.callback(
    [Output('textarea-input-program1', 'value'),
    Output('textarea-input-program2', 'value'),
    Output('textarea-input-program3', 'value')],
    [Input('data-dropdown-program', 'value'), Input('submit_button', 'n_clicks')],
    [State('textarea-input-program1', 'value')])
def callback_a(x, y, input_program):
    global prev_click


    #input_program = ''
    input_assem   = ''
    input_assem_text   = ''
    fol_txt = ''
    if y is None:
       
       input_program = constructProgram(readingFile( x ))
       
    elif prev_click < y:
       prev_click = y
       if input_program is not None and input_program.strip()!='':
          writtingFile( 'tempprogram.c' , input_program )
          filename='tempprogram.c'
          result1 = translation2wasm(filename)
          if result1 is not None:
             input_assem_text = result1 
             f,o,a,cm,assert_list,assume_list,assert_key,fol_txt = webasm.translation()

    else:
       input_program = constructProgram(readingFile( x ))

    return input_program,input_assem_text,fol_txt


if __name__ == '__main__':
    app.run_server(debug=True)
