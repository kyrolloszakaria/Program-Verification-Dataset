# Program-Verification-Dataset
### This is a repo containing training data for LLM to be trained on program verification in Dafny and Python

# Dafny dataset
search prompt: language:Dafny requires ensures invariant decreases assert assume
search results: https://github.com/search?q=language%3ADafny+requires+ensures+invariant+decreases+assert+assume&type=code&p=1
search progress: finished page 1 out of 5

1. from dafny main repo: https://github.com/dafny-lang/dafny/tree/master/Source/IntegrationTests
2. lightening verifier repo: https://github.com/danyangz/lightning/blob/b969467e1bd79fcedabdc4e30fd86d69eb7025b6/verifier/undo_log.dfy 
3. vetri-titan: https://github.com/secure-foundations/veri-titan/tree/1c0e64fd6728b20a0e123c4f77d925436a6f32c5/script/old/dfy_model 
4. pregel algorithms: https://github.com/fmlab-iis/Pregel/tree/1c029a151cfcfdd400c4c1a8a7ae634bf1988e58/notes
5. basic examples: https://github.com/stqam/dafny/tree/76b9858a7e5fc3442cb745dd707385af285f8ca7 
6. NFS system verification: https://github.com/mit-pdos/daisy-nfsd/tree/98434db21451b76c700dcf5783b2bca00a63c132/src/fs
7. Advanced examples: https://github.com/wilcoxjay/notes
8. Course materials: https://github.com/RU-Automated-Reasoning-Group/CS515/tree/c924d6ce1be00eac54d2dbd6c2f78f30dabe3c76/Dafny
9. mathematical objects verification: https://github.com/tchajed/dafny-syntax-tutorial/tree/0e8a97b6b5be66d5eb05f125b13e0ad0d71ba57b/src 
10. verified algorithms: https://github.com/Nangos/verified-algorithms/tree/f782876dce9c5a174071d39b847e73c822dc1fb1/dafny 
11. vampire project: https://github.com/AbanobTawfik/SENG2011-Project/tree/8eb38b7c24c1345217a86205389a559ce7486ad1/Dafny 
12. fat node: https://github.com/kumom/dafny-fatnode/tree/10a6748c5f63607cf1661f018e239af8569421de 
13. algorithms and leetcode: https://github.com/hath995/dafny/tree/489ad55832cc054ac2b104a2e4ac548fa0a9154f
14. variant examples: https://github.com/ggrov/tacny/tree/7d5fd08c5eb5a86a495484020e31069954fd2210/examples/dafny/variant
15. vetri-sparse: https://github.com/volodeyka/veri-sparse/tree/b0308b52dcfaf2c818782cc02c926bf96014895e/dafny 

Total files are: 1660 (The numbers are approximates due to readme files and so)
Classify the codes into:
- Simple but descent category represents stand-alone code. For example: known algorithms that are implemented in dafny with program verification.
- Overcomplicated category represents a verification part of a big project where the dafny files depend on other components (classes, methods) from the project to work.

A. Simple but descent: 4, 5, 7, 8, 9, 10, 12, 13, 14 (330)
B. Overcomplicated: 1 (stand alone),2,3, 6, 10, 15 (1172)



