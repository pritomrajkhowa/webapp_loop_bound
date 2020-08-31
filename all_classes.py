"""
#Export Maps
"""

class exportMapclass(object):
        def __init__(self, ExportMemory, ExportFunction, ExportGlobal):
                self.ExportMemory = ExportMemory
                self.ExportFunction = ExportFunction
                self.ExportGlobal = ExportGlobal

        def getExportMemory(self):
                return self.ExportMemory

        def setExportMemory(self, ExportMemory):
	        self.ExportMemory = ExportMemory

        def getExportFunction(self):
                return self.ExportFunction

        def setExportFunction(self, ExportFunction):
	        self.ExportFunction = ExportFunction

        def getExportGlobal(self):
                return self.ExportGlobal

        def setExportGlobal(self, ExportGlobal):
	        self.ExportGlobal = ExportGlobal




"""
#Memory Variable
"""

class memoryclass(object):
        def __init__(self, memoryList):
                self.memoryList = memoryList

        def getMemoryList(self):
                return self.memoryList

        def getMemoryList(self, memoryList):
	        self.memoryList = memoryList



"""
#Global Variable
"""

class globalclass(object):
        def __init__(self, globalname, varType, mul, value):
                self.globalname = globalname
                self.varType = varType
                self.mul = mul
                self.value = value
        def getGlobalname(self):
                return self.globalname
        def getVarType(self):
                return self.varType
        def getMul(self):
                return self.mul
        def getValue(self):
                return self.value
        def setGlobalname(self, globalname):
	        self.globalname = globalname
        def setVarType(self, varType):
	        self.varType = varType
        def setMul(self, mul):
	        self.mul = mul
        def setValue(self, value):
	        self.value = value


"""
#Table Type
"""

class tableclass(object):
        def __init__(self, tablename, tableInfo):
                self.tablename = tablename
                self.tableInfo = tableInfo
        def getTablename(self):
                return self.tablename
        def getTableInfo(self):
                return self.tableInfo
        def setTablename(self, tablename):
	        self.tablename = tablename
        def setTableInfo(self, tableInfo):
	        self.tableInfo = tableInfo




"""
#Class of Variable
"""
class variableclass(object):
        def __init__(self, variablename, variableType):
                self.variablename = variablename
                self.variableType = variableType
        def getVariablename(self):
                return self.variablename
        def getVariableType(self):
                return self.variableType
        def setVariablename(self, variablename):
	        self.variablename=variablename
        def setVariableType(self, variableType):
	        self.variableType=variableType


"""
#Function Type
"""
class functionclass(object):
        def __init__(self, funname, returnList, inputList):
                self.funname = funname
                self.returnList = returnList
                self.inputList = inputList
        def getFunname(self):
                return self.funname
        def getReturnList(self):
                return self.returnList
        def getInputList(self):
                return self.inputList
        def setFunname(self, funname):
	        self.funname=funname
        def setReturnList(self, returnList):
	        self.returnList=returnList
        def getInputList(self, inputList):
	        self.inputList=inputList



