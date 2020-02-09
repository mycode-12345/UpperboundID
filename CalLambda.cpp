#include<stdio.h>
#define m 4 //S-box size
#define t 32 //number of S-boxes
#define n 128 //block size
unsigned char P[n][n]={0};//representation of P-layer over F_2, an n*n matrix
int main()
{
	unsigned int Lambda(unsigned char P[n][n]);//calculate the number of rounds that can propagate any nonzero input pattern to an all-one pattern, return it.
	void Midori128();//generate the P[][] of the P-layer of Midori128
	Midori128();//take Midori128 as an example
	printf("For Midori128, %d rounds can propagate any nonzero input pattern to an all-one output pattern.\n",Lambda(P));
	return 1;
}
void Midori128()
{
	/* generate the P[][] of the P-layer of Midori128
	*/
	unsigned char s[16]={0},temp0[16],temp1[16];
	unsigned int i,j,k,u;
	for(i=0;i<16;i++)
	{
		for(k=0;k<8;k++)
		{
			s[i]=1<<k;
			for(j=0;j<16;j++)
			{
				if((j%4)==0) temp0[j]=(s[j]&0x55)^((s[j]&0xa0)>>4)^((s[j]&0xa)<<4);
				if((j%4)==1) temp0[j]=((s[j]&0x60)>>5)^((s[j]&0x88)>>1)^((s[j]&0x17)<<3);
				if((j%4)==2) temp0[j]=((s[j]&0xec)>>2)^((s[j]&0x11)<<2)^((s[j]&0x2)<<6);
				if((j%4)==3) temp0[j]=((s[j]&0x80)>>7)^((s[j]&0x40)>>3)^((s[j]&0x3b)<<1)^((s[j]&0x4)<<5);
			}
			temp1[0]=temp0[0],temp1[1]=temp0[10],temp1[2]=temp0[5],temp1[3]=temp0[15];
			temp1[4]=temp0[14],temp1[5]=temp0[4],temp1[6]=temp0[11],temp1[7]=temp0[1];
			temp1[8]=temp0[9],temp1[9]=temp0[3],temp1[10]=temp0[12],temp1[11]=temp0[6];
			temp1[12]=temp0[7],temp1[13]=temp0[13],temp1[14]=temp0[2],temp1[15]=temp0[8];
			for(j=0;j<8;j++)
			{
				temp0[j*4]=temp1[j*4+1]^temp1[j*4+2]^temp1[j*4+3];
				temp0[j*4+1]=temp1[j*4]^temp1[j*4+2]^temp1[j*4+3];
				temp0[j*4+2]=temp1[j*4]^temp1[j*4+1]^temp1[j*4+3];
				temp0[j*4+3]=temp1[j*4]^temp1[j*4+1]^temp1[j*4+2];
			}
			for(j=0;j<16;j++)
			{
				if((j%4)==0) temp1[j]=(temp0[j]&0x55)^((temp0[j]&0xa0)>>4)^((temp0[j]&0xa)<<4);
				if((j%4)==1) temp1[j]=((temp0[j]&0xb8)>>3)^((temp0[j]&0x44)<<1)^((temp0[j]&0x3)<<5);
				if((j%4)==2) temp1[j]=((temp0[j]&0x80)>>6)^((temp0[j]&0x44)>>2)^((temp0[j]&0x3b)<<2);
				if((j%4)==3) temp1[j]=((temp0[j]&0x80)>>5)^((temp0[j]&0x76)>>1)^((temp0[j]&0x8)<<3)^((temp0[j]&0x1)<<7);
			}
			for(j=0;j<16;j++)
			{
				for(u=0;u<8;u++)
				{
					if(temp1[j]&(1<<u)) P[i*8+k][j*8+u]=1;
					else P[i*8+k][j*8+u]=0;
				}
			}
		}
		s[i]=0;
	}
}
unsigned int Lambda(unsigned char P[n][n])
{
	/* calculate the number of rounds that can propagate any nonzero input pattern to an all-one pattern, return it.
	*/
	unsigned int PatternExpansion_improved(unsigned char P[n][n],unsigned char a[t],unsigned char b[t]);
	unsigned char a[t]={0},b[t]={0};
	unsigned int r,r_max=1,wb;
	unsigned int i,j;
	for(i=0;i<t;i++)
	{
		a[i]=1;
		r=1;
		while(1)
		{
			wb=PatternExpansion_improved(P,a,b);
			if(wb==t)
			{
				//printf("%d\n",r);
				goto next_a;
			}
			for(j=0;j<t;j++) a[j]=b[j];
			r++;
		}
next_a:r_max=(r_max>r)?r_max:r;
		for(j=0;j<t;j++) a[j]=0;
	}
	return r_max;
}
unsigned int PatternExpansion_improved(unsigned char P[n][n],unsigned char a[t],unsigned char b[t])//with optimization
{
	/*P must be invertible!
	Calculate a possible heavier output pattern b for input pattern a after the P matrix, and return the hamming weight of b
	*/
	unsigned int Block_rank_P(unsigned char P[n][n],unsigned char a[t],unsigned int Rset[]);
	unsigned int Block_rank_Pa(unsigned char Pa[n][n],unsigned int num_col,unsigned int Rset[]);
	unsigned int add(unsigned char Pa[n][n],unsigned int wa,unsigned int Rset[],unsigned char b[t]);
	//unsigned char Pr[n][n]={0};//reduced matrix by input pattern 'a' and free variables
	unsigned char Pa[n][n]={0};//selected matrix by input pattern 'a'
	unsigned char free[n]={0};//indicate the location of free variables, 1-nonfree variable, 0-free variable
	unsigned int Rset[n];//set of row indexs of maximal independent set
	unsigned int rank;//
	unsigned int num_col=0;
	unsigned int i,j,u;
	unsigned int wa=0,wb;
	for(i=0;i<t;i++) wa=wa+a[i],b[i]=0;
	//get the block_rank of Pa "rank" and maximal independent set "Rset[]"
	wb=Block_rank_P(P,a,Rset);
	//only when wa>1, need free variables:?. No! for retain "non-reduce of patterns" when wa=1 to wa>1, for any wa!=0, we use wa free variables!
	//get the index set of free variables, there maybe exist better choice of free variables...
	for(j=0;j<n;j++) {if((j%m!=m-1)&&a[j/m]) free[j]=1;}
	//get the reduced linear equation system, and corresponding block_rank;
	for(i=0;i<wa*m;i++)
	{
		u=0;
		for(j=0;j<n;j++)
		{
			//if(free[j])	Pr[Rset[i]][u++]=P[Rset[i]][j];
			if(free[j])	Pa[Rset[i]][u++]=P[Rset[i]][j];
		}
	}
	//wb=Block_rank_Pa(Pr,wa*m-wa,Rset);
	wb=Block_rank_Pa(Pa,wa*m-wa,Rset);
	//get the output pattern b
	for(i=0;i<wa*m-wa;i++) b[Rset[i]/m]=1; 
	//add m-1 odd vector
	for(i=0;i<n;i++)
	{
		u=0;
		for(j=0;j<n;j++)
		{
			if(a[j/m]) Pa[i][u++]=P[i][j];
		}
	}
	wb=add(Pa,wa,Rset,b);
	//add m-1 odd vector
	return wb;
}
unsigned int Block_rank_Pa(unsigned char Pa[n][n],unsigned int num_col,unsigned int Rset[])
{
	/*Pa must be column fullrank, for left num_col columns
	Find a maximal independent set of row vectors in the left num_col columns of Pa, such that its related row-block is maximized.
	Rset[] is the index set of those maximal independent set, and return the rowblock-rank of these vectors.
	*/
	//unsigned char Pa[n][n]={0};//rearranged P matrix by input pattern a[]
	unsigned int act_row[n]={0};//indicate the activeness of each row of Pa
	unsigned int wei_rowblock[t]={0};//indicate the number of active rows in each rowblock;
	int wei_order[t];//order the indexes of active rowblocks in ascending, note that inactive rowblocks and scaned rowblocks are tagged by '-1'
	unsigned int tag[t];//tag[i] stores the index of the next scan-needed row in the i-th rowblock;
	unsigned int order;
	unsigned char temp;
	unsigned int i,j,k,u,s;
	unsigned int wb=0;
	unsigned int rank_rowblock=0;
	for(i=0;i<n;i++)
	{
		for(j=0;j<num_col;j++) act_row[i]=act_row[i]|Pa[i][j];
	}
	for(i=0;i<n;i++) wei_rowblock[i/m]=wei_rowblock[i/m]+act_row[i];
	for(i=0;i<t;i++) {if(wei_rowblock[i]) wb++;}
	for(i=0;i<t;i++) wei_order[i]=-1,tag[i]=m*i;
	u=0;
	for(j=1;j<=m;j++)
	{
		for(i=0;i<t;i++)
		{
			if(wei_rowblock[i]==j) wei_order[u++]=i;
		}
	}
	order=0;
	for(j=0;j<num_col;)
	{
		while(1)
		{
next_rowblock:if(order>=wb) order=0;
			while(wei_order[order]==-1)
			{
				order++;
				if(order>=wb) order=0;
				//Notice: possibe dead loop when wei_order is filled up with -1.
			}
			i=tag[wei_order[order]];
			while(1)
			{
				for(s=j;s<num_col;s++)
				{
					if(Pa[i][s])
					{
						Rset[j]=i;
						for(k=s+1;k<num_col;k++)
						{
							if(Pa[i][k])
							{
								for(u=0;u<n;u++) Pa[u][k]=Pa[u][k]^Pa[u][s];
							}
						}
						for(u=0;u<n;u++)
						{
							temp=Pa[u][j],Pa[u][j]=Pa[u][s],Pa[u][s]=temp;
						}
						//j++;
						if(j==num_col-1)
						{
							//calculate block rank;
							for(u=0;u<t;)
							{
								for(k=0;k<num_col;k++)
								{
									if(Rset[k]/m==u)
									{
										rank_rowblock++;
										goto next_u;
									}
								}
next_u:							u++;
							}
							//calculate block rank;
							return rank_rowblock;
						}
						if((i%m)==m-1) wei_order[order++]=-1;
						else tag[wei_order[order++]]=i+1;
						goto next_column;//also next_rowblock
					}
				}
				if((i%m)==m-1)
				{
					wei_order[order++]=-1;
					goto next_rowblock;
				}
				i++;
			}
		}
next_column:j++;
	}
}
unsigned int Block_rank_P(unsigned char P[n][n],unsigned char a[t],unsigned int Rset[])
{
	/* P must be invertible!
	Choosing the columnblocks of P by the pattern a, and get Pa[][];
	Find a maximal independent set of row vectors of Pa, and Rset[] stores the indexs of these row vectors;
	Return the rowblock rank of this set.
	*/
	unsigned int Block_rank_Pa(unsigned char Pa[n][n],unsigned int num_col,unsigned int Rset[]);
	unsigned char Pa[n][n]={0};//rearranged P matrix by input pattern a[]
	unsigned int num_col=0;//num of chosen columns in P by a;
	unsigned int s,i,j;
	s=0;
	for(j=0;j<n;j++)
	{
		if(a[j/m])
		{
			num_col++;
			for(i=0;i<n;i++)
			{
				Pa[i][s]=P[i][j];
			}
			s++;
		}
	}
	return Block_rank_Pa(Pa,num_col,Rset);
}
unsigned int add(unsigned char Pa[n][n],unsigned int wa,unsigned int Rset[],unsigned char b[t])
{
	//unsigned char Pa[n][n]={0};
	unsigned char tag[n]={0};
	unsigned char temp;
	unsigned int i,j,k,u;
	unsigned int num_add;
	unsigned int wb;
	unsigned int num_Rset,num_col;
	num_col=wa*m;
	num_Rset=wa*m-wa;
	for(i=0;i<num_Rset;i++) tag[Rset[i]]=1;
	//transform base into standard base
	for(i=0;i<num_Rset;i++)
	{
		//if 0,exchange
		if(Pa[Rset[i]][i]==0)
		{
			for(j=i+1;j<num_col;j++)
			{
				if(Pa[Rset[i]][j])
				{
					for(k=i;k<num_Rset;k++) temp=Pa[Rset[k]][i],Pa[Rset[k]][i]=Pa[Rset[k]][j],Pa[Rset[k]][j]=temp;
				}
			}
		}
		//elimination
		for(j=i+1;j<num_Rset;j++)
		{
			if(Pa[Rset[j]][i])
			{
				//elimination
				for(k=i;k<num_col;k++) Pa[Rset[j]][k]=Pa[Rset[j]][k]^Pa[Rset[i]][k];
				tag[Rset[j]]=tag[Rset[j]]^tag[Rset[i]];
			}
		}
	}
	//get the odd/even representation of other vector by base
	for(i=0;i<t;i++)
	{
		if(b[i]==0)
		{
			for(j=0;j<m;j++)
			{
				for(k=0;k<num_Rset;k++)
				{
					if(Pa[i*m+j][k])
					{
						Pa[i*m+j][k]=0;
						for(u=num_Rset;u<num_col;u++) Pa[i*m+j][u]=Pa[i*m+j][u]^Pa[Rset[k]][u];
						tag[i*m+j]=tag[i*m+j]^tag[Rset[k]];
					}
				}
				for(;k<num_col;k++)
				{
					if(Pa[i*m+j][k])
					{
						tag[i*m+j]=0;
						break;
					}
				}
			}
		}
	}
	num_add=0;
	for(i=0;i<t;i++)
	{
		if(b[i]==0)
		{
			for(j=0;j<m;j++)
			{
				if(tag[i*m+j]) 
				{
					b[i]=1;
					num_add++;
					if(num_add==m-1)
					{
						goto add_over;
					}
					break;
				}
			}
		}
	}
add_over:wb=0;
	for(i=0;i<t;i++) wb=wb+b[i];
	return wb;
}
