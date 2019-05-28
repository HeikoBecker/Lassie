import pdb
import argparse
import json
from collections import defaultdict
import csv




def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--query_log_file", dest="queryLogFile", required = True)
    parser.add_argument("--query_response_file", dest="queryResponseFile", required = True)
    parser.add_argument("--cleaned_output_file", dest = "outputFile")
    parser.add_argument("--statistics_file", dest = "statisticsFile", default = "statistics.csv")
    parser.add_argument("--group", dest = "group")
    keyValues = set()
    args, unknown = parser.parse_known_args()
    
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
    idStartedExperiment = defaultdict(lambda: False)
    with open(queryLogFile) as inputFile:
        with open(outputFile, "w") as outputFile:
            for line in inputFile:
                jsonInput = json.loads(line)
                key = jsonInput["sessionId"]
                if idStartedExperiment[key] == False and "start" in jsonInput["q"]:
                    idStartedExperiment[key] = True
                    keyValues.add(key)
                
                if idStartedExperiment[key] == False:
                    continue
                if jsonInput["q"].startswith("(:context"):
                    continue
                
                query = jsonInput["q"]
                
                if query.startswith("(:def"):
                    numberOfDefinitions[key] += 1
        
                        
                outputFile.write(json.dumps(jsonInput)+"\n")
    idStartedExperiment = defaultdict(lambda: False)
    with open(queryResponseFile) as responseFile:
        
        for line in responseFile:
            response = json.loads(line)
            key = response["sessionId"]
            if "start" in response["q"]:
                idStartedExperiment[key] = True
            if idStartedExperiment[key] == False:
                continue

            kindOfQuery = response["stats"]["status"]
            authorInfo = response["stats"]["author"]
            
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
        writer = csv.writer(csvfile)
        writer.writerow(["id", "group", "number of queries", "length of queries", "number of tokens", "number of definitions", "number of unparsable queries",\
                         "number of induced queries", "number of core language queries", "length of successful queries", "tokens in successful", "queries by others", "queries by self"])
        for keyId in keyValues:
            writer.writerow([keyId, group, numberOfQueries[keyId], lengthOfQueries[keyId], numberOfTokens[keyId], numberOfDefinitions[keyId],\
                              kindsOfQueries["Nothing"][keyId], kindsOfQueries["Induced"][keyId], kindsOfQueries["Core"][keyId], \
                              lengthOfSuccessfulQueries[keyId], numberOfTokensInSuccessful[keyId], authors["Other"][keyId], authors["Self"][keyId]])
            
                
    

if __name__ == '__main__':
    main()