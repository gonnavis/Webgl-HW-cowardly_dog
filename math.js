let dot = (a,b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
let scale = (v, s) => [ s * v[0] , s * v[1] , s * v[2] ];
let norm = v => Math.sqrt(dot(v,v));
let normalize = v => scale(v, 1 / norm(v));
