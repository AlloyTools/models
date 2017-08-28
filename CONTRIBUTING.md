# Contributing to AlloyTools Alloy Models

Found a bug, issue, or shortcoming in of the existing models? Created an interesting model? We would love your fixes and feedback.

## Reporting Issues

Reporting [issues](https://github.com/AlloyTools/org.alloytools.alloy.models/issues). Please provide the version of Alloy you are using. If you can provide examples, then that would be very much appreciated. When you provide a PR, our gratidtude will have no bounds.

## Adding a new Model

If you want to add a new model then you need to find a good place for it. Each model should be in a directory that has two levels: class and 

repository is limited to 2 levels: class and instance. For example, `util/java` or `algorithms/dijkstra`. In this directory you can place the model files. If needed, sub directories can be used. Some hints:

* Do not use spaces in the class, instance, and file names. Preferably use short java fully qualified like like names. That is, if you need multiple parts use a dot ('.') to separate the parts.
* Try to reuse directories, this makes things easier to find
* Do not use overly generic names, someone looking for a model should find it quickly.
* Provide a readme.md file that explains the context of the model

## License

All models must be submitted under the Apache 2.0 license.

## Workflow

If you have a small fix, then just edit the model and commit it. Github will automatically fork the repo and create a pull request. 

### Regular contributions

For more extensive and (can we dream?) regular contributions we suggest to clone the repository. We use [git triangular workflow](https://www.sociomantic.com/blog/2014/05/git-triangular-workflow/).
This means that no one, not even the maintainers of this site, push contributions directly into the [main org.alloytools.alloy.models repo](https://github.com/AlloyTools/org.alloytools.alloy.models). All contribution come in through pull requests (PR).
So each contributor will need to [fork the main models repo](https://github.com/AlloyTools/org.alloytools.alloy.models/fork)
on GitHub. All contributions are made as commits to your fork. Then you submit a
pull request to have them considered for merging into the main Bnd repo.

### Setting up the triangular workflow

After forking the main Bnd repo on GitHub, you can clone the main repo to your system:

    git clone https://github.com/AlloyTools/org.alloytools.alloy.models.git

This will clone the main repo to a local repo on your disk and set up the `origin` remote in Git.
Next you will set up the the second side of the triangle to your fork repo.

    cd org.alloytools.alloy.models
    git remote add fork git@github.com:<github-user>/org.alloytools.alloy.models.git

Make sure to replace the URL with the SSH URL to your fork repo on GitHub. Then we configure
the local repo to push your commits to the fork repo.

    git config remote.pushdefault fork

So now you will pull from `origin`, the main repo, and push to `fork`, your fork repo.
This option requires at least Git 1.8.4. It is also recommended that you configure

    git config push.default simple

unless you are already using Git 2.0 where it is the default.

Finally, the third side of the triangle is pull requests from your fork repo to the
main repo.

## Contribution guidelines

### Pull requests are always welcome

We are always thrilled to receive pull requests, and do our best to
process them as fast as possible. Not sure if that typo is worth a pull
request? (Again, you can edit the files directly on Github!) Do it! We will appreciate it.

If your pull request is not accepted on the first try, don't be
discouraged! If there's a problem, hopefully you
received feedback on what to improve.

### Create issues...

Any significant improvement should be documented as [a GitHub
issue](https://github.com/bndtools/bnd/issues) before anybody
starts working on it.

### ...but check for existing issues first!

Please take a moment to check that an issue doesn't already exist
documenting your bug report or improvement proposal. If it does, it
never hurts to add a quick "+1" or "I have this problem too". This will
help prioritize the most common problems and requests.

### Sign your work

The sign-off is a simple line at the end of the commit message
which certifies that you wrote it or otherwise have the right to
pass it on as an open-source patch.  The rules are pretty simple: if you
can certify the below (from
[developercertificate.org](http://developercertificate.org/)):

```
Developer Certificate of Origin
Version 1.1

Copyright (C) 2004, 2006 The Linux Foundation and its contributors.
660 York Street, Suite 102,
San Francisco, CA 94110 USA

Everyone is permitted to copy and distribute verbatim copies of this
license document, but changing it is not allowed.


Developer's Certificate of Origin 1.1

By making a contribution to this project, I certify that:

(a) The contribution was created in whole or in part by me and I
    have the right to submit it under the open source license
    indicated in the file; or

(b) The contribution is based upon previous work that, to the best
    of my knowledge, is covered under an appropriate open source
    license and I have the right under that license to submit that
    work with modifications, whether created in whole or in part
    by me, under the same open source license (unless I am
    permitted to submit under a different license), as indicated
    in the file; or

(c) The contribution was provided directly to me by some other
    person who certified (a), (b) or (c) and I have not modified
    it.

(d) I understand and agree that this project and the contribution
    are public and that a record of the contribution (including all
    personal information I submit with it, including my sign-off) is
    maintained indefinitely and may be redistributed consistent with
    this project or the open source license(s) involved.
```

then you just add a line to end of the git commit message:

    Signed-off-by: Joe Smith <joe.smith@email.com>

using your real name. Sorry, no pseudonyms or anonymous contributions.

Many Git UI tools have support for adding the `Signed-off-by` line to the end of your commit
message. This line can be automatically added by the `git commit` command by using the `-s` option.
