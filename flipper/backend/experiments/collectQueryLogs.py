import pdb
import argparse
import json
from collections import defaultdict
import csv


"""
the whole "special condition" part is becuase there were few mistakes in the experiment
 1. I didn't reset the log file after the tutorial. therefore, it contained their tutorial attempts. that's why we have startingPoints that describe where for each participant the tutorial stops
 2. we were short on time and then two participants had a break before continuing. That assigned them different session ids. THat's why I have artificial session ids now (P1, P2, P3)
 
 ---
 
 also, for it is changed for the second group:
 1. one participant continued experimenting even after he finished all the tasks (that's why now it is eliminated if it exceeds the count of his last query)
"""
# sessionIds = {"kamqupluqc":"A1", "4whvuab45y":"A2", "c70jstrl5l":"A2", "mrb7cylagj":"A3", "g8o4jp76a":"A3"}
# startingPoints = {"A1" : 334, "A3" : 210, "A2":345}
# endPoints = {"A1":20000, "A2":20000, "A3":20000}
# keyValues = ["A1", "A2", "A3"]

# sessionIds = {"vmdwsrp3a4":"BP1", "brv6imuw4t":"BP2", "x1z4imvyyc":"BP3", "70wnvrj0uk":"BP4" }
# endPoints = {"BP1" : 679, "BP3" : 2000, "BP2":2000, "BP4":2000}
# startingPoints = {"BP1" : 0, "BP3" : 0, "BP2":0, "BP4":0}
# keyValues = ["BP1", "BP2", "BP3", "BP4"]

# sessionIds = {"kzfpiapflq":"A4", "rdd5eqad7b":"BP5", "moyetrwi6i":"BP6" }
# endPoints = {"A4" : 20000, "BP5" : 20000, "BP6":20000}
# startingPoints = {"A4" : 0, "BP5" : 0, "BP6":0}
# keyValues = ["A4", "BP5", "BP6"]

sessionIds = {"0til5ny2qg":"C1", "q173uk0av1":"C2", "spt84ba5di":"C3" }
endPoints = {"C1" : 20000, "C2" : 20000, "C3":20000}
startingPoints = {"C1" : 0, "C2" : 0, "C3":0}
keyValues = ["C1", "C2", "C3"]
unknownIds = set()
def transformIncomingJson(jsonInput, specialConditions = False):
    
    if jsonInput['q'].startswith("(:context"):
        return None
    if specialConditions == True:
        try:
            id = sessionIds[jsonInput["sessionId"]]
        except:
            if jsonInput["sessionId"] not in unknownIds:
                print(jsonInput["sessionId"])
                print("unkonwn id")
                unknownIds.add(jsonInput["sessionId"])
            return None
        if jsonInput["count"] <= startingPoints[id] or jsonInput["count"] >= endPoints[id]:
            return None
        else:
            jsonInput["sessionId"] = id
            return jsonInput
    else:
        return jsonInput
        
        
        
        
    

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--special_conditions", dest="specialConditions", action='store_true', default = False)
    parser.add_argument("--query_log_file", dest="queryLogFile", required = True)
    parser.add_argument("--query_response_file", dest="queryResponseFile", required = True)
    parser.add_argument("--cleaned_output_file", dest = "outputFile")
    parser.add_argument("--statistics_file", dest = "statisticsFile", default = "statistics.csv")
    parser.add_argument("--group", dest = "group")
    
    args, unknown = parser.parse_known_args()
    
    specialConditions = args.specialConditions
    queryLogFile = args.queryLogFile
    queryResponseFile = args.queryResponseFile
    outputFile = args.outputFile
    statisticsFile = args.statisticsFile
    group = args.group
    
    if group == None:
        raise Exception("no group was given")
    
    lengthOfQueries = defaultdict(lambda:0)
    lengthOfSuccessfulQueries = defaultdict(lambda:0)
    numberOfQueries = defaultdict(lambda:0)
    numberOfTokens = defaultdict(lambda:0)
    numberOfTokensInSuccessful = defaultdict(lambda:0)
    numberOfDefinitions = defaultdict(lambda:0)
    
    kindsOfQueries = {}
    kindsOfQueries["Core"] = defaultdict(lambda:0)
    kindsOfQueries["Induced"] = defaultdict(lambda:0)
    kindsOfQueries["Nothing"] = defaultdict(lambda:0)
    
    authors = {}
    authors["None"] = defaultdict(lambda:0)
    authors["Self"] = defaultdict(lambda:0)
    authors["Other"] = defaultdict(lambda:0)
    
    
    if outputFile == None:
        outputFile = "cleaned_"+queryLogFile
    with open(queryLogFile) as inputFile:
        with open(outputFile, "w") as outputFile:
            for line in inputFile:
                transformedJson = transformIncomingJson(json.loads(line), specialConditions)
                if transformedJson == None:
                    continue
                query = transformedJson["q"]
                key = transformedJson["sessionId"]
                if query.startswith("(:def"):
                    numberOfDefinitions[key] += 1
        
                        
                    outputFile.write(json.dumps(transformedJson)+"\n")
    with open(queryResponseFile) as responseFile:
        for line in responseFile:
            response = transformIncomingJson(json.loads(line), specialConditions)
            if response == None:
                continue
            kindOfQuery = response["stats"]["status"]
            authorInfo = response["stats"]["author"]
            key = response["sessionId"]
            
            query = response["q"]
            if query.startswith("(:q"):
                characterCount = len(query) - 7
                tokenCount = len( query.split()) - 1 
                    
                lengthOfQueries[key] += characterCount
                numberOfTokens[key] += tokenCount
                numberOfQueries[key] += 1
                if kindOfQuery != "Nothing":
                    lengthOfSuccessfulQueries[key] += characterCount
                    numberOfTokensInSuccessful[key] += tokenCount
            
            kindsOfQueries[kindOfQuery][key] += 1 
            authors[authorInfo][key] += 1
                
    with open(statisticsFile, "a") as csvfile:
        pdb.set_trace()
        writer = csv.writer(csvfile)
        for keyId in keyValues:
            writer.writerow([keyId, group, numberOfQueries[keyId], lengthOfQueries[keyId], numberOfTokens[keyId], numberOfDefinitions[keyId],\
                              kindsOfQueries["Nothing"][keyId], kindsOfQueries["Induced"][keyId], kindsOfQueries["Core"][keyId], \
                              lengthOfSuccessfulQueries[keyId], numberOfTokensInSuccessful[keyId], authors["Other"][keyId], authors["Self"][keyId]])
            
                
    

if __name__ == '__main__':
    main()