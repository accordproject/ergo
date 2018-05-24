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

# Exit on first error, print all commands.
set -ev
set -o pipefail

git checkout master
git pull origin master

npm run pkgbump
TARGET_VERSION=$( jq -r '.version' lerna.json )
RELEASE_BRANCH="release-${TARGET_VERSION}"
git checkout -b ${RELEASE_BRANCH}

lerna publish --conventional-commits -m 'chore(release): publish %s' --force-publish=* --allow-branch ${RELEASE_BRANCH} --repo-version ${TARGET_VERSION} --yes

git add mechanization/Version.v
git commit -m "chore(release): Bump Ergo source version" -s
git push --set-upstream origin ${RELEASE_BRANCH}

echo "Publish of ${TARGET_VERSION} successful."
echo "Now open a pull request to merge branch ${RELEASE_BRANCH} into master."
echo "https://github.com/accordproject/ergo/compare/${RELEASE_BRANCH}?expand=1"
