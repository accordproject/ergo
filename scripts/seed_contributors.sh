#!/bin/bash

#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
USER=$1
TOKEN=$2
CURRENT_REPO=$3
ORGANIZATION=accordproject

# needed to avoid the rate limit
export PRIVATE_TOKEN=$TOKEN

CONTRIBUTORS=()

# Get contributors for each repo
REPO_CONTRIBUTORS=( $(curl -u ${USER}:${TOKEN} -s https://api.github.com/repos/${ORGANIZATION}/${CURRENT_REPO}/stats/contributors | jq -r '.[] | .author.login') )

# Concatenate the existing contributors with the new ones
CONTRIBUTORS=("${CONTRIBUTORS[@]}" "${REPO_CONTRIBUTORS[@]}")

# Remove duplicates
CONTRIBUTORS=($( echo "${CONTRIBUTORS[@]}" | tr ' ' '\n' | sort -u | tr '\n' ' '))

for i in "${!CONTRIBUTORS[@]}"; do 
    echo "${CONTRIBUTORS[$i]}"
    node  "./node_modules/all-contributors-cli/dist/cli.js"  add ${CONTRIBUTORS[$i]} doc
done

node  "./node_modules/all-contributors-cli/dist/cli.js" generate