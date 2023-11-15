
const w = 128;
const h = 128;
//function gridToPixelLeft(x,y) {
    //return [w*x/2+y*h/4, -w*x/2+y*h/4];
//}

function gridToPixelRight(x,y) {
    return [[w*x/2-w*y/2],[h*x/4+h*y/4]];
}

console.log([[0,0],[1,0],[2,0],[0,1],[0,2]].map(elems => gridToPixelRight.apply(null,elems)));
