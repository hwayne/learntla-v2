I've run into two problems with including specs:

1. TLA+ requires files to list the filename in the spec. eg if you have a file `xyz.py`, you MUST write ```---- MODULE xyz ----` at the beginning of the file. This means that you cannot compile PlusCal specs to a "different file", they must always be generated inline. This *in turn* means that you can't include PlusCal specs directly, since they'll have hundreds of lines of TLA+ translation that clutter up the codeblock.

2. I want to include metadata with each spec, like what the state space should look like for each model run. And I want this to remain in sync, so that I don't have inconsistencies when I change specs. I can include this as a YAML header to the spec, but then it would be visible to website readers, and I don't want that either.

So this is where I'm storing raw specs with metadata. I also have a script that converts a spec into a new file *and updates the MODULE string*, while also updating metadata and stripping out PlusCal translations.

