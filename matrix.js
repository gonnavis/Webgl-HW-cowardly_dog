
//---------- PRIMITIVE MATRIX PRIMITIVE OPERATIONS ------------

// MATRIX INDEXING IS COLUMN MAJOR:
//
//  0  4  8 12
//  1  5  9 13
//  2  6 10 14
//  3  7 11 15

let matrix_identity = () => {
   return [1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1];
}

let matrix_translate = (x,y,z) => {
   if (y === undefined) {
      z = x[2];
      y = x[1];
      x = x[0];
   }
   let m = matrix_identity();
   m[12] = x;
   m[13] = y;
   m[14] = z;
   return m;
}

let matrix_rotateX  = theta   => {
   let m = matrix_identity();
   m[ 5] =  Math.cos(theta);
   m[ 6] =  Math.sin(theta);
   m[ 9] = -Math.sin(theta);
   m[10] =  Math.cos(theta);
   return m;
}
let matrix_rotateY  = theta   => {
   let m = matrix_identity();
   m[10] =  Math.cos(theta);
   m[ 8] =  Math.sin(theta);
   m[ 2] = -Math.sin(theta);
   m[ 0] =  Math.cos(theta);
   return m;
}
let matrix_rotateZ  = theta   => {
   let m = matrix_identity();
   m[ 0] =  Math.cos(theta);
   m[ 1] =  Math.sin(theta);
   m[ 4] = -Math.sin(theta);
   m[ 5] =  Math.cos(theta);
   return m;
}
let matrix_scale    = (x,y,z) => {
   if (y === undefined)
      y = z = x;
   let m = matrix_identity();
   m[ 0] = x;
   m[ 5] = y;
   m[10] = z;
   return m;
}
let matrix_multiply = (a,b)   => {
   let m = [];
   for (let col = 0 ; col < 4 ; col++)
   for (let row = 0 ; row < 4 ; row++) {
      let value = 0;
      for (let i = 0 ; i < 4 ; i++)
         value += a[4*i + row] * b[4*col + i];
      m.push(value);
   }
   return m;
}
let matrix_transform = (m,p) => {
   let x = p[0], y = p[1], z = p[2], w = p[3] === undefined ? 1 : p[3];
   let q = [ m[0]*x + m[4]*y + m[ 8]*z + m[12]*w,
             m[1]*x + m[5]*y + m[ 9]*z + m[13]*w,
             m[2]*x + m[6]*y + m[10]*z + m[14]*w,
             m[3]*x + m[7]*y + m[11]*z + m[15]*w ];
   return p[3] === undefined ? [ q[0]/q[3],q[1]/q[3],q[2]/q[3] ] : q;
}
let matrix_inverse = src => {
  let dst = [], det = 0, cofactor = (c, r) => {
     let s = (i, j) => src[c+i & 3 | (r+j & 3) << 2];
     return (c+r & 1 ? -1 : 1) * ( (s(1,1) * (s(2,2) * s(3,3) - s(3,2) * s(2,3)))
                                 - (s(2,1) * (s(1,2) * s(3,3) - s(3,2) * s(1,3)))
                                 + (s(3,1) * (s(1,2) * s(2,3) - s(2,2) * s(1,3))) );
  }
  for (let n = 0 ; n < 16 ; n++) dst.push(cofactor(n >> 2, n & 3));
  for (let n = 0 ; n <  4 ; n++) det += src[n] * dst[n << 2];
  for (let n = 0 ; n < 16 ; n++) dst[n] /= det;
  return dst;
}
let matrix_perspective = fl => {
  return [ 1,0,0,0, 0,1,0,0, 0,0,-1,-1/fl, 0,0,0,1 ];
}
let matrix_transpose = m =>
  [ m[0],m[4],m[8],m[12], m[1],m[5],m[9],m[13], m[2],m[6],m[10],m[14], m[3],m[7],m[11],m[15] ];


//---------- MATRIX OBJECT CLASS ------------

let Matrix = function() {
   let top = 0, m = [ matrix_identity() ];
   this.identity  = ()      => m[top] = matrix_identity();
   this.translate = (x,y,z) => m[top] = matrix_multiply(m[top], matrix_translate(x,y,z));
   this.rotateX   = theta   => m[top] = matrix_multiply(m[top], matrix_rotateX(theta));
   this.rotateY   = theta   => m[top] = matrix_multiply(m[top], matrix_rotateY(theta));
   this.rotateZ   = theta   => m[top] = matrix_multiply(m[top], matrix_rotateZ(theta));
   this.scale     = (x,y,z) => m[top] = matrix_multiply(m[top], matrix_scale(x,y,z));
   this.value     = ()      => m[top];
   this.save      = ()      => { m[top+1] = m[top].slice(); top++; }
   this.restore   = ()      => --top;
}

let M = new Matrix();

