import requests
import pdb
import argparse
import json

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--server_url", dest="serverUrl", default = 'http://139.19.186.111:8410/sempre')
    parser.add_argument("--file_to_replay", dest = "fileToReplay", required=True)
    
    
    args, unknown = parser.parse_known_args()
    format = "list2Json"
    
    with open(args.fileToReplay) as queryFile:
        for line in queryFile:
            data = json.loads(line)
            
            sessionId = data['sessionId']
            r = requests.post(args.serverUrl, params = { 'format':format, 'q':data['q'], 'sessionId': sessionId})
            print(r.text)
            

if __name__ == '__main__':
    main()