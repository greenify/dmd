#!/bin/bash

################################################################################
# Required packages
# python python-yaml make gdb g++ gcc libcurl dmd (optional)
################################################################################

cat << 'EOF'
steps:
  - command: |
      uname -a
      make --version
      \${SHELL} --version || true
      c++ --version
      ld -v
      ! command -v gdb &>/dev/null || gdb --version
      dmd --version || true
    label: "Print envs"
    env:
      DETERMINISTIC_HINT: 1

  - command: |
      set -uexo pipefail
      origin_repo=dmd # TODO
      origin_target_branch="\$BUILDKITE_PULL_REQUEST_BASE_BRANCH"
      if [ -z "\$origin_target_branch" ] ; then
        origin_target_branch="\$BUILDKITE_BRANCH"
      fi
      echo \$origin_target_branch

      for dir in dmd druntime phobos tools dub ; do
          rm -rf \$dir
          if [ "\$origin_repo" == "\$dir" ] ; then
            # we have already cloned this repo, so let's use this data
            mkdir -p \$dir
            cp -r \$(ls -A | grep -v dmd) \$dir
          else
            branch=\$(git ls-remote --exit-code --heads https://github.com/dlang/\$dir "\${origin_target_branch}" > /dev/null || echo "master")
            git clone -b "\${branch:-master}" --depth 1 https://github.com/dlang/\$dir
          fi
      done

      for dir in dmd druntime phobos ; do
          make -C \$dir -f posix.mak AUTO_BOOTSTRAP=1 --jobs=4
      done

      # build dub
      (cd dub && DMD='gdb -return-child-result -q -ex run -ex bt -batch --args dmd' ./build.sh)

      # build tools
      make -C tools -f posix.mak RELEASE=1 --jobs=4

      # distribution
      rm -rf distribution
      mkdir -p distribution/{bin,imports,libs}
      cp --archive --link dmd/generated/linux/release/64/dmd dub/bin/dub tools/generated/linux/64/rdmd distribution/bin/
      cp --archive --link phobos/etc phobos/std druntime/import/* distribution/imports/
      cp --archive --link phobos/generated/linux/release/64/libphobos2.{a,so,so*[!o]} distribution/libs/
      echo '[Environment]' >> distribution/bin/dmd.conf
      echo 'DFLAGS=-I%@P%/../imports -L-L%@P%/../libs -L--export-dynamic -L--export-dynamic -fPIC' >> distribution/bin/dmd.conf

      tar cvfz distribution.tgz distribution
    label: "Build"
    artifact_paths: "distribution.tgz"

  - wait
EOF

################################################################################
# Add your project here
################################################################################
projects=(
    "atilaneves/unit-threaded"
    "msoucy/dproto"
    "higgsjs/Higgs"
    "vibe-d/vibe.d+vibe-core-base"
)

use_travis_test_script()
{
cat << 'EOF1'
      cat > travis.sh << 'EOF2'
      import os, sys, yaml
      def dub_test():
        print("dub test --compiler=\$DC")
        sys.exit(0)
      if not os.path.isfile('.travis.yml'):
        dub_test()
      script = yaml.load(open('.travis.yml', 'r')).get('script', '')
      if isinstance(script, list):
        script = '\n'.join(script)
      if len(script) > 0:
        print(script)
      else:
        dub_test()
      EOF2
      python travis.sh
      python travis.sh | bash
EOF1
    #echo "      dub test"
}

for fullProject in "${projects[@]}" ; do
    repoDir=$(basename "$project")
    project=$(echo "$fullProject" | sed "s/\([^+]*\)+.*/\1/")
cat << EOF
  - command: |
      set -uexo pipefail
      repo_url=https://github.com/${project}
      repoDir=$(basename "$project")
EOF
cat << 'EOF'
      export PATH="\$PWD/distribution/bin:\${PATH:-}"
      export LIBRARY_PATH="\$PWD/distribution/libs:\${LIBRARY_PATH:-}"
      export LD_LIBRARY_PATH="\$PWD/distribution/libs:\${LD_LIBRARY_PATH:-}"
      buildkite-agent artifact download distribution.tgz .
      tar xfz distribution.tgz
      rm -rf \${repoDir}
      tag=\$(git ls-remote --tags \${repo_url} | sed -n 's|.*refs/tags/\(v\?[0-9]*\.[0-9]*\.[0-9]*\$\)|\1|p' | sort --version-sort | tail -n 1)
      git clone -b "\${tag:-master}" --depth 1 \$repo_url
      cd \${repoDir}
EOF
################################################################################
# Add custom build instructions here
################################################################################
    case "$fullProject" in

    vibe-d/vibe.d+vibe-core-base):
        echo "      VIBED_DRIVER=vibe-core PARTS=builds,unittests ./travis-ci.sh"
        ;;
    higgsjs/Higgs):
        echo '      make -C source test DC=\$DC'
        ;;
    *)
        use_travis_test_script
        ;;
    esac
################################################################################
cat << EOF
    label: "${fullProject}"
    env:
      DETERMINISTIC_HINT: 1
      DC: dmd
      DMD: dmd
EOF
done
