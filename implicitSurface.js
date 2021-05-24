
function implicitSurfaceTriangleMesh(n, implicitFunction, computeWeights, isFaceted) {

   // DEFINE SOME USEFUL FUNCTIONS

   let cross     = (a,b) => [ a[1]*b[2] - a[2]*b[1], a[2]*b[0] - a[0]*b[2], a[0]*b[1] - a[1]*b[0] ];
   let dot       = (a,b) =>   a[0]*b[0] + a[1]*b[1] + a[2]*b[2];
   let normalize =   a   => { let s = Math.sqrt(dot(a,a)); return [ a[0]/s, a[1]/s, a[2]/s ]; }

   // HERE IS WHERE MOST OF THE WORK HAPPENS

   let marchingTetrahedra = function(V, ni, nj) {

      // CONVENIENCE FUNCTIONS TO COMPUTE (i,j,k) FROM VOLUME INDEX n

      function n2i(n) { return  n             % ni; }
      function n2j(n) { return (n / dj >>> 0) % nj; }
      function n2k(n) { return  n / dk >>> 0      ; }

      // ADD A VERTEX AND RETURN A UNIQUE ID FOR THAT VERTEX

      function E(a, b) {
         if (a > b) { let tmp = a; a = b; b = tmp; }
         let ai = n2i(a), aj = n2j(a), ak = n2k(a),
             bi = n2i(b), bj = n2j(b), bk = n2k(b);

         let m = (n << 6) + (ai & bi ?  1 << 6 : ai      | bi << 3)
                          + (aj & bj ? dj << 6 : aj << 1 | bj << 4)
                          + (ak & bk ? dk << 6 : ak << 2 | bk << 5);

         // ADD TO VERTEX ARRAY ONLY THE FIRST TIME THE VERTEX IS ENCOUNTERED

         if (vertexID[m] === undefined) {
            vertexID[m] = P.length / 3;
            let t = -V[n+a] / (V[n+b] - V[n+a]),
                c = (i,a,b) => (i + a + t * (b-a)) / ni * 2 - 1;
            P.push( c(i,ai,bi), c(j,aj,bj), c(k,ak,bk) );
         }

         return vertexID[m];
      }

      // CASE WHERE WE ADD ONE TRIANGLE IN A TETRAHEDRON

      let tri = (a, b, c, d) => T.push(E(a,b), E(a,c), E(a,d));

      // CASE WHERE WE ADD TWO TRIANGLES IN A TETRAHEDRON

      let quad = (a, b, c, d) => {
         let bc = E(b,c), ad = E(a,d);
         T.push(bc, E(a,c), ad,  ad, bc, E(b,d));
      }

      // DECLARE VARIABLES

      let nk = V.length / (ni * nj), di = 1, dj = ni, dk = ni * nj;
      let dij = di + dj, dik = di + dk, djk = dj + dk, dijk = di + dj + dk;
      let P = [], T = [], vertexID = [], i, j, k, m = 0, n, S = [0,di,dij,dijk];
      let lo = new Array(nj * nk),
          hi = new Array(nj * nk);

      // THE SIX POSSIBLE INTERMEDIATE PATHS THROUGH A TETRAHEDRON

      let S1 = [di , dj , dk , di , dj , dk ];
      let S2 = [dij, djk, dik, dik, dij, djk];

      // THERE ARE 16 CASES TO CONSIDER

      let cases = [ [0         ], [1, 0,1,2,3], [1, 1,2,0,3], [2, 0,1,2,3],
                    [1, 2,3,0,1], [2, 0,2,3,1], [2, 1,2,0,3], [1, 3,1,2,0],
                    [1, 3,0,2,1], [2, 0,3,1,2], [2, 1,3,2,0], [1, 2,1,0,3],
                    [2, 2,3,0,1], [1, 1,3,0,2], [1, 0,3,2,1], [0         ], ];

      // FOR EACH (Y,Z), DON'T DO ANY WORK OUTSIDE OF X RANGE WHERE SURFACE MIGHT BE
   
      for (k = 0 ; k < nk ; k++)
         for (j = 0 ; j < nj ; j++, m++) {
            let n0 = m * ni, n1 = n0 + ni - 1;
            for (n = n0 ; n <= n1 && V[n] > 0 ; n++) ;
            lo[m] = Math.max(0, n-1 - n0);
            for (n = n1 ; n >= n0 && V[n] > 0 ; --n) ;
            hi[m] = Math.min(ni-1, n+1 - n0);
         }

      // FOR ALL Y AND Z IN THE VOLUME

      for (k = 0 ; k < nk - 1 ; k++) {
         let i0, i1, m = k * nj, n1, s0, s1;
         for (j = 0 ; j < nj - 1 ; j++, m++) {
            i0 = Math.min(lo[m], lo[m+1], lo[m+ni], lo[m+1+ni]);
            i1 = Math.max(hi[m], hi[m+1], hi[m+ni], hi[m+1+ni]);

            // GO THROUGH RANGE OF X WHERE THE SURFACE MIGHT BE (IE: WITH ANY POSITIVE VALUES)

            if (i0 <= i1) {
               n  = m * ni + i0;
               n1 = m * ni + i1;
               s0 = (V[n]>0) + (V[n+dj]>0) + (V[n+dk]>0) + (V[n+djk]>0);
               for (i = i0 ; n <= n1 ; i++, n++, s0 = s1) {

                  // FOR EACH CUBE

                  s1 = (V[n+di]>0) + (V[n+dij]>0) + (V[n+dik]>0) + (V[n+dijk]>0);
                  if (s0 + s1 & 7) {
                     let C03 = (V[n] > 0) << 0 | (V[n+dijk] > 0) << 3;

                     // CYCLE THROUGH THE SIX TETRAHEDRA THAT TILE THE CUBE

                     for (let p = 0 ; p < 6 ; p++) {
                        let C = cases [ C03 | (V[n+S1[p]] > 0) << 1 | (V[n+S2[p]] > 0) << 2 ];

                        // FOR EACH TETRAHEDRON, OUTPUT EITHER ZERO, ONE OR TWO TRIANGLES

                        if (C[0]) {       // C[0] == number of triangles to be created.
                           S[1] = S1[p];  // assign 2nd and 3rd corners of simplex.
                           S[2] = S2[p];
                           (C[0]==1 ? tri : quad)(S[C[1]], S[C[2]], S[C[3]], S[C[4]]);
                        }
                     }
                  }
               }
            }
         }
      }

      // MAKE SURE ALL TRIANGLE VERTICES ARE LISTED IN COUNTERCLOCKWISE ORDER

      for (let m = 0 ; m < T.length ; m += 3) {
         let a = 3 * T[m], b = 3 * T[m+1], c = 3 * T[m+2],
             n = Math.floor(ni*(P[a  ]+1)/2)      +
                 Math.floor(ni*(P[a+1]+1)/2) * dj +
                 Math.floor(ni*(P[a+2]+1)/2) * dk,
             u = cross([P[b] - P[a], P[b+1] - P[a+1], P[b+2] - P[a+2]],
                       [P[c] - P[b], P[c+1] - P[b+1], P[c+2] - P[b+2]]),
             v = [ V[n+1] - V[n], V[n+dj] - V[n], V[n+dk] - V[n] ];
         if (dot(u, v) < 0) { let tmp = T[m]; T[m] = T[m + 2]; T[m + 2] = tmp; }
      }

      // RETURN POINTS AND TRIANGLES

      return [P, T];
   }

   // SAMPLE THE VOLUME

   let F = [];
   for (let i = 0 ; i < n ; i++)
      F.push((i - n/2) / (n/2));

   // OPTIMIZE BY IGNORING ROWS IN WHICH ALL VALUES ARE NEGATIVE

   let isRow = [];
   for (let k = 0 ; k < n ; k += 2) {
      isRow[k] = [];
      for (let j = 0 ; j < n ; j += 2) {
         for (let i = 0 ; i < n ; i += 2)
	    if (isRow[k][j] = implicitFunction(F[i],F[j],F[k]) > -.5)
	       break;
         isRow[k][j+1] = isRow[k][j];
      }
      isRow[k+1] = isRow[k];
   }
   for (let k = 0 ; k < n-1 ; k++) {
      for (let j = 0   ; j <  n ; j++) if (isRow[k][j]) isRow[k][j-1] = true;
      for (let j = n-2 ; j >= 0 ; j--) if (isRow[k][j]) isRow[k][j+1] = true;
   }
   for (let j = 0 ; j < n-1 ; j++) {
      for (let k = 0   ; k <  n ; k++) if (isRow[k][j]) isRow[k-1][j] = true;
      for (let k = n-2 ; k >= 0 ; k--) if (isRow[k][j]) isRow[k+1][j] = true;
   }

   // FILL THE VOLUME WITH VALUES FROM THE IMPLICIT FUNCTION

   let volume = [];
   for (let k = 0 ; k < n ; k++)
   for (let j = 0 ; j < n ; j++)
      if (isRow[k][j])
         for (let i = 0 ; i < n ; i++)
	    volume.push(implicitFunction(F[i], F[j], F[k]));
      else
         for (let i = 0 ; i < n ; i++)
	    volume.push(-1);

   // FIND ALL VERTICES AND TRIANGLES IN THE VOLUME
   
   let VT = marchingTetrahedra(volume, n, n);
   let V = VT[0];
   let T = VT[1];

   // COMPUTE SURFACE NORMALS

   let N = new Array(V.length);
   for (let i = 0 ; i < V.length ; i += 3) {
      let x = V[i], y = V[i+1], z = V[i+2], e = .001,
          f0 = implicitFunction(x  ,y  ,z  ),
          fx = implicitFunction(x+e,y  ,z  ),
          fy = implicitFunction(x  ,y+e,z  ),
          fz = implicitFunction(x  ,y  ,z+e),
          normal = normalize([f0-fx,f0-fy,f0-fz]);
      for (let j = 0 ; j < 3 ; j++)
         N[i+j] = normal[j];
   }

   // CONSTRUCT AND RETURN THE TRIANGLES MESH

   let mesh = [];
   for (let i = 0; i < T.length; i += 3) {
      let a = 3 * T[i    ],
          b = 3 * T[i + 1],
          c = 3 * T[i + 2];

      if (isFaceted) {
         let normal = normalize([N[a  ]+N[b  ]+N[c  ],
                                 N[a+1]+N[b+1]+N[c+1],
                                 N[a+2]+N[b+2]+N[c+2]]);
         N[a  ] = N[b  ] = N[c  ] = normal[0];
         N[a+1] = N[b+1] = N[c+1] = normal[1];
         N[a+2] = N[b+2] = N[c+2] = normal[2];
      }

      mesh.push( V[a],V[a+1],V[a+2] , N[a],N[a+1],N[a+2] , 1,0,0,0,0,0 ,
                 V[b],V[b+1],V[b+2] , N[b],N[b+1],N[b+2] , 1,0,0,0,0,0 ,
                 V[c],V[c+1],V[c+2] , N[c],N[c+1],N[c+2] , 1,0,0,0,0,0 );

      if (computeWeights) {
         let n = mesh.length;
         computeWeights(mesh, n - 3 * 12 + 6, V[a],V[a+1],V[a+2]);
         computeWeights(mesh, n - 2 * 12 + 6, V[b],V[b+1],V[b+2]);
         computeWeights(mesh, n - 1 * 12 + 6, V[c],V[c+1],V[c+2]);
      }
   }
   return new Float32Array(mesh);
}

// CREATE SPACE FILLING FUNCTIONS THAT BLEND TOGETHER SIMPLE GEOMETRIC SHAPES

function Blobs() {

   const SPHERE = 0;
   const CYLINDER = 1;
   const CUBE = 2;

   this.useSoftMin = state => isSoftMin = state;

   let isSoftMin = false;

   let minfunc = (a,b,c) => {
      if (isSoftMin) {
         a = Math.exp(1-a*a);
         b = Math.exp(1-b*b);
         c = c === undefined ? 0 : Math.exp(1-c*c);
         return 1 - Math.log(a + b + c);
      }
      else
         return c === undefined ? Math.min(a, b) : Math.min(a, b, c);
   }

   let data, t;
   let blob = (data, x, y, z) => {

      let type = data.type;

      x -= data.center[0];
      y -= data.center[1];
      z -= data.center[2];

      let A = data.ABC[0], a = A[0] * x + A[1] * y + A[2] * z, da = A[3], aa = a*a,
          B = data.ABC[1], b = B[0] * x + B[1] * y + B[2] * z, db = B[3], bb = b*b,
          C = data.ABC[2], c = C[0] * x + C[1] * y + C[2] * z, dc = C[3], cc = c*c;

      switch (data.type) {
      case SPHERE:
         {
            let t1 = 1 - (aa + bb + cc);
            let t0 = 1 - (aa / da + bb / db + cc / dc);
            t = t0 / (t0 - t1);
         }
         break;

      case CYLINDER:
         {
            let rrab = aa + bb, rrc = cc,
                tab1 = 1 - (aa + bb),
                tab0 = 1 - (aa / da + bb / db),
		tc1  = 1 - cc,
                tc0  = 1 - cc / dc,
                tab  = Math.max(0, tab0 / (tab0 - tab1)),
                tc   = Math.max(0, tc0  / (tc0  - tc1 ));
	    t = minfunc(tab, tc);
         }
         break;

      case CUBE:
         {
            let ta1 = 1 - aa, ta0 = 1 - aa / da,
	        tb1 = 1 - bb, tb0 = 1 - bb / db,
		tc1 = 1 - cc, tc0 = 1 - cc / dc,
                ta  = ta0 / (ta0 - ta1),
                tb  = tb0 / (tb0 - tb1),
                tc  = tc0 / (tc0 - tc1);
	    t = minfunc(ta, tb, tc);
         }
         break;
      }

      t = Math.max(0, t);
      t = t * t;
      if (t > 1)
         t = 2 - 1/t;

      return t * data.sign;
   }

   this.clear = () => data = [];

   this.addBlob = (type, _M, d, material) => {
      let M = _M.slice();
      if (d === undefined)
         d = 0.5;
      let x = M[12], y = M[13], z = M[14];
      M[12] = M[13] = M[14] = 0;
      let m = matrix_transpose(matrix_inverse(M));
      let A = matrix_transform(m, [1,0,0,0]);
      let B = matrix_transform(m, [0,1,0,0]);
      let C = matrix_transform(m, [0,0,1,0]);
      let ad = Math.abs(d);
      A[3] = 1 + ad * norm([A[0],A[1],A[2]]);
      B[3] = 1 + ad * norm([B[0],B[1],B[2]]);
      C[3] = 1 + ad * norm([C[0],C[1],C[2]]);
      A[3] *= A[3];
      B[3] *= B[3];
      C[3] *= C[3];
      data.push({
         type    : type,
         center  : [x,y,z],
         ABC     : [A,B,C],
         sign    : Math.sign(d),
      });
   }

   this.setData = (_data) => {
      data = [];
      for (let n = 0 ; n < _data.length ; n++)
         this.addBlob(_data[n][0], _data[n][1], _data[n][2]);
   }

   this.eval = (x,y,z) => {
      value = -1;
      for (let n = 0 ; n < data.length ; n++)
         value += blob(data[n], x,y,z);
      return value;
   }

   this.computeWeights = (dst, i, x,y,z) => {

      // CREATE AN INDEXED ARRAY OF NON-ZERO WEIGHTS

      let index = [], value = [], sum = 0;
      for (let n = 0 ; n < data.length ; n++) {
         let v = blob(data[n], x,y,z);
	 if (v > 0) {
            index.push(n);
            value.push(v);
	    sum += v;
	    if (index.length == 6)
	       break;
         }
      }

      // PACK INDEX AND WEIGHT INTO INT+FRACTION PORTIONS OF THE SAME NUMBER

      for (let j = 0 ; j < value.length ; j++)
         dst[i + j] = index[j] + Math.max(0, Math.min(.999, value[j] / sum));

      for (let j = value.length ; j < 6 ; j++)
         dst[i + j] = -1;
   }
}
