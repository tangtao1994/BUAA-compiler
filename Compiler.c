 #include<stdio.h>
#include"PL0.h"


int enterTable(char *name,varKind type,identKind kind,int level,int address,int arrayFlag,int AddFlag);
void backEnter(int tx,varKind type,identKind kind,int arrayFlag);
void enterConst(varKind type,int Inum,double Fnum,char Cnum);
void enterArray(int tx,varKind type,int len);
void enterFunc(int tx,int Num,varKind ReturnVal);
void enterPro(int tx,int Num);
int DeclarePosition(char *name,int lev);//����ʱ���
int StatementPosition(char *name,int lev);//��䲿�ֲ��
void printTableInfo();//��ӡ���ű���Ϣ��tableInfo.txt


/*******************************�ʷ�����******************************/
int getSym();
int getch();
void error(int index);


/******************************�﷨����******************************/
void block(int level,int *address);
void ConstDeclaration(int level,int *address);
void Constdeclaration(int level);
void VarDeclaration(int level,int *address);
void Vardeclaration(int level,int *address);
int FuncProDeclare(int level,int *address);
int parameter(int level,int *address);
void Sentence(int level);
void SentenceIf(int level);
void Condition(int level);
void SentenceAssign(int level);
void SentenceRead(int level);
void SentenceWrite(int leve);
void SentenceBegin(int level);
void SentenceRepeat(int level);
void SentenceFor(int level);
void PopTable(int begin,int end);
void CallFunc(int level);
void CallPro(int level);

/*�����⼸�������������������ǵķ���ֵ�ж����ǵ�����*/
varKind factor();
varKind expression();
varKind term();




/************************P-codeָ�����************************/
void generate(fct funcName,int lev,double add);
void interpret();
void listcode();
int base(int l);



void error(int index)
{
	/*���������Ϣ���ڼ��У��ڼ�λ����������*/
	printf("ERROR! Line:%d,Pos:%d,%s\n",lx,cc+1,ERROR_MESSAGE[index]);
	errNum++;
}
/*��ȡһ���ַ�*/
int getch()
{
	int i;

	if(cc==ll)//��ȡ����ǰ�еĽ���
	{
		lx++;
		/*�ж��Ƿ�����ļ��Ľ�β*/
		if(fgets(line,MAXLINE,fileIn)==NULL)
		{
			printf("�Ѿ������ļ��Ľ�β��\n");
			fclose(fileIn);
			return 0;
		}
		/*��ll��cc����Ϊ0*/
		ll=0;
		cc=0;
		for(i=0;i<MAXLINE;i++)
			if(line[i]=='\0')//char��������'\0'��β
			{
				ll=i;
				break;
			}
	}
	/*��С�ڵ���*/
	if(cc<ll)
		ch=line[cc++];
	return 1;

}

/*ȡһ��symbol�����ǹ涨��ÿ�β����궼Ԥȡһ���ַ�ch*/
int getSym()
{
	int k=0,i,reserveFlag=0;//reserveFlag���ڱ�ʶ�Ƿ��Ǳ�ʶ��

	while(ch==' '||ch== '\t'||ch=='\n')//��ȥ�ո���Ʊ���Լ����з�
		getch();

	/*��ʶ�������Ǳ�����*/
	if(isalpha(ch))
	{0
		buf[k++]=ch;
		getch();
		while(isalpha(ch)||isdigit(ch))//��ʶ���м�����������
		{
			buf[k++]=ch;
			getch();
		}
		buf[k]='\0';
		for(i=0;i<RESERVENUM;i++)
			if(strcmp(reservedWord[i],buf)==0)//�Ǳ�����
			{
					sym=reservedSym[i];//��sym��Ϊ��Ӧ�ı�����
					reserveFlag=1;
					break;
			}
		if(reserveFlag==0)
			sym=identsym;//��sym��Ϊ��ʶ��
		strcpy(id,buf);//�ѵ�ǰ�ı�ʶ������id��
		return 1;
	}

	/*������*/
	else if(isdigit(ch))
	{
		buf[k++]=ch;
		getch();
		while(isdigit(ch))
		{
			buf[k++]=ch;//�ѵ�ǰ�������ַ�װ��buf������
			getch();
		}
		if(ch=='.')//��real��
		{
			buf[k++]=ch;
			getch();
			while(isdigit(ch))
			{
				buf[k++]=ch;
				getch();
			}
			buf[k]='\0';
			FNumber=atof(buf);//�ѵ�ǰ�����ַ���INumber��
			sym=floatNumber;//��sym��Ϊʵ��
			
		}
		else//��integer��
		{
			buf[k]='\0';
			INumber=atoi(buf);//�ѵ�ǰ�����ַ���FNumber��
			sym=intNumber;//��sym��Ϊ����
		}
		return 1;
	}

	/*���ַ�*/
	else if(ch=='\'')//�˴�Ҫʹ��ת���ַ�
	{
		getch();
		if(isdigit(ch)||isalpha(ch))
			buf[k++]=ch;
		else 
		{
			buf[k]='\0';
			error(0);//�ַ��д��ڷǷ�����
			return 0;
		}
		buf[k]='\0';
		getch();
		if(ch!='\'')//�����һ���ַ����ǵ�����
		{
			error(1);
			return 0;
		}
		sym=character;
		getch();//Ԥȡһ���ַ�
		return 1;
	}
	/*���ַ���*/
	else if(ch=='\"')//�˴�ʹ��ת���ַ�
	{
		getch();
		while(ch!='\"')//�ķ�����Ҫ���ַ����п��������֡���ĸ�Ϳո�	while(isdigit(ch)||isalpha(ch)||ch==' ')
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
		}
		if(ch=='\"')//�ַ�����˫���Ž�β
		{
			sym=stringsym;
			getch();
			return 1;
		}
		else//���������ķǷ��ַ�
		{
			error(2);
			return 0;
		}
	}
	else if(ch=='+')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=addsym;
		getch();
		return 1;
	}
	else if(ch=='-')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=subsym;
		getch();
		return 1;
	}
	else if(ch=='*')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=mulsym;
		getch();
		return 1;
	}
	else if(ch=='/')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=divsym;
		getch();
		return 1;
	}
	else if(ch==':')
	{
		buf[k++]=ch;
		getch();
		if(ch=='=')
		{
			buf[k++]=ch;
			sym=becomes;
			buf[k]='\0';
			getch();
			return 1;
		}
		else
		{
			sym=colonsym;
			buf[k]='\0';
			return 1;
		}	
	}
	else if(ch=='=')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=eql;
		getch();
		return 1;
	}
	else if(ch=='<')
	{
		buf[k++]=ch;
		buf[k]='\0';
		getch();
		if(ch=='=')//С�ڵ���
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
			sym=leq;
			return 1;
		}
		else if(ch=='>')//������
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
			sym=neq;
			return 1;
		}
		else//С��
		{
			sym=lss;
			return 1;
		}
	}
	else if(ch=='>')
	{
		buf[k++]=ch;
		buf[k]='\0';
		getch();
		if(ch=='=')//���ڵ���
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
			sym=geq;
			return 1;
		}
		else//����
		{
			sym=gtr;
			return 1;
		}
	}
	else if(ch=='=')//����
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=eql;
		getch();
		return 1;
	}
	else if(ch==',')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=comma;
		getch();
		return 1;
	}
	else if(ch=='.')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=period;
		getch();
		return 1;
	}
	else if(ch=='(')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=lparen;
		getch();
		return 1;
	}
	else if(ch==')')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=rparen;
		getch();
		return 1;
	}
	else if(ch=='[')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=lbracket;
		getch();
		return 1;
	}
	else if(ch==']')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=rbracket;
		getch();
		return 1;
	}
	else if(ch==';')
	{
		buf[k++]=ch;
		buf[k]='\0';
		sym=semicolon;
		getch();
		return 1;
	}
	error(3);//��������������򱨴�
	return 0;
}
/*����P-codeָ��*/
void generate(fct funcName,int lev,double add)
{
	codeTable[codeindex].f=funcName;
	codeTable[codeindex].a=add;
	codeTable[codeindex].l=lev;
	codeindex++;
}
/*�ǼǷ��ű�*/
int enterTable(char *name,varKind type,identKind kind,int level,int address,int arrayFlag,int AddFlag)
{
	tableindex++;
	strcpy(Table[tableindex].name,name);
	Table[tableindex].type=type;
	Table[tableindex].kind=kind;
	Table[tableindex].level=level;
	Table[tableindex].address=address;/* �˴������Ǻ�������ڣ����Ǻ������ֵ�λ�á�
									   * �Ժ������Ҫ�õ���������ڣ���ô�ɺ����ĵ�һ��������λ��
									   * ���Ϻ����ǼǱ��иú�����size���ɵõ�
									   */
	Table[tableindex].arrayFlag=arrayFlag;
	Table[tableindex].AddUse=AddFlag;
	if(kind==varsym&&arrayFlag==1)//���������
		Table[tableindex].index=arrayindex;//��arrayindex�����÷��ű����index����,�����Ժ�Ĳ���
	else if(kind==constsym)//����ǳ���
		Table[tableindex].index=constindex;//��constindex�����÷��ű����index����,�����Ժ�Ĳ���
	else if(kind==funcsym)//����Ǻ���
		Table[tableindex].index=funcindex;//��funcindex�����÷��ű����index����,�����Ժ�Ĳ���
	else if(kind==prosym)//����ǹ���
		Table[tableindex].index=proindex;//��proindex�����÷��ű����index����,�����Ժ�Ĳ���
	return address-1;
}
/*������ű��������ͺ�����*/
void backEnter(int tx,varKind type,identKind kind,int arrayFlag)
{
	Table[tx].type=type;
	Table[tx].kind=kind;
	Table[tx].arrayFlag=arrayFlag;
}
/*�Ǽǳ������ű�*/
void enterConst(varKind type,int Inum,float Fnum,char Cnum)
{
	constTable[constindex].type=type;
	constTable[constindex].valueC=Cnum;
	constTable[constindex].valueI=Inum;
	constTable[constindex].valueF=FNumber;
	constindex++;
}
/*�Ǽ�������ű�*/
void enterArray(int tx,varKind type,int len)
{
	Table[tx].type=type;
	arrayTable[Table[tx].index].type=type;
	arrayTable[Table[tx].index].len=len;
}
/*�ǼǺ�����*/
void enterFunc(int tx,int Num,varKind ReturnVal)
{
	funcTable[Table[tx].index].paraNum=Num;
	funcTable[Table[tx].index].ReturnVal=ReturnVal;
}
/*�Ǽǹ��̱�*/
void enterPro(int tx,int Num)
{
	proTable[Table[tx].index].paraNum=Num;
}
/*���̺��������󣬽��ֲ�������������ջ*/
void PopTable(int begin,int end)
{
	int i;
	for(i=begin;i<=end;i++)
		Table[i].level=-1;
}

int DeclarePosition(char *name,int lev)//����ʱ�����ַ����е�λ��
{
	int i;
	for(i=tableindex;i>0;i--)//�ӷ��ű�ĺ�����ǰ���
	{
		if(strcmp(name,Table[i].name)==0&&lev==Table[i].level)
			return i;
	}
	return 0;//û���ҵ�
}

int StatementPosition(char *name,int lev)//��䲿�ֲ����ַ����е�λ�ã����Ե��ñȵ�ǰ��ε͵ı�ʶ��
{
	int i;
	for(i=tableindex;i>0;i--)
	{
		if(strcmp(name,Table[i].name)==0&&lev>=Table[i].level&&Table[i].level!=-1)
			return i;
	}
	return 0;
}



/* ��������ok
 *<��������>::=<��ʶ��>��[+| -] (<�޷�������>| <�޷���ʵ��>)|<�ַ�>
 */
void Constdeclaration(int level)
{
	getSym();
	if(sym==identsym)
	{
		if(DeclarePosition(buf,level)!=0)//�Ѿ������
			error(5);
		else
		{
			getSym();
			if(sym==eql)
			{
				getSym();
				if(sym==addsym)
				{
					getSym();
					if(sym==intNumber)
					{
						enterTable(id,intkind,constkind,level,0,0,0);//�ǼǷ��ű��������֣����ͣ����࣬��Σ���ַ���Ƿ�������
						Table[tableindex].index=constindex;
						enterConst(intkind,INumber,0.0,' ');
					}
					else if(sym==floatNumber)
					{
						enterTable(id,realkind,constkind,level,0,0,0);//�ǼǷ��ű��������֣����ͣ����࣬��Σ���ַ���Ƿ�������
						Table[tableindex].index=constindex;
						enterConst(realkind,0,FNumber,' ');
					}
				}
				else if(sym==subsym)
				{
					getSym();
					if(sym==intNumber)
					{
						INumber=-INumber;//���ſ�ͷ������ȡ��
						enterTable(id,intkind,constkind,level,0,0,0);//�ǼǷ��ű��������֣����ͣ����࣬��Σ���ַ���Ƿ�������
						Table[tableindex].index=constindex;
						enterConst(intkind,INumber,0.0,' ');
					}
					else if(sym==floatNumber)
					{
						FNumber=-FNumber;
						enterTable(id,realkind,constkind,level,0,0,0);//�ǼǷ��ű��������֣����ͣ����࣬��Σ���ַ���Ƿ�������
						Table[tableindex].index=constindex;
						enterConst(realkind,0,FNumber,' ');
					}
				}
				else if(sym==intNumber)
				{
					enterTable(id,intkind,constkind,level,0,0,0);//�ǼǷ��ű��������֣����ͣ����࣬��Σ���ַ���Ƿ�������	
					Table[tableindex].index=constindex;
					enterConst(intkind,INumber,0.0,' ');
				}
				else if(sym==floatNumber)
				{
					enterTable(id,realkind,constkind,level,0,0,0);//�ǼǷ��ű��������֣����ͣ����࣬��Σ���ַ���Ƿ�������	
					Table[tableindex].index=constindex;
					enterConst(realkind,0,FNumber,' ');
				}
				else if(sym==character)
				{
					enterTable(id,charkind,constkind,level,0,0,0);
					Table[tableindex].index=constindex;
					enterConst(charkind,0,0.0,buf[0]);
				}
				else 
				{
					error(6);//���������г��ֲ��Ϸ��ɷ֣�
				}
			}
			else
				error(7);//ȱ�ٵȺ�
		}
	}
	else 
	{
		error(8);//���Ǳ�ʶ�����߱�ʶ���д��ڲ��Ϸ�����
	}
	getSym();
	return ;
}

/* ����˵��
 *<����˵��>::=<��ʶ��>{,<��ʶ��>}:<����>
 *
 *<����>::=<��������>|array'['<�޷�������>']' of <��������>
 */
void Vardeclaration(int level,int *address)
{
	int i,tx0;//��Ϊһ�����͵ı��������кܶ࣬����������tx0��¼�ʼ�ı�����tableindexֵ�����ں���ķ�������
	if(sym==identsym)
	{
		if(DeclarePosition(buf,level)!=0)//�Ѿ������
			error(5);
		else
		{
			enterTable(id,intkind,varkind,level,*address,1,0);//�˴���������һ�����ͣ�����intkind
			tx0=tableindex;
			(*address)++;
			getSym();
			while(sym==comma)
			{
				getSym();
				if(sym==identsym)
				{
					if(DeclarePosition(buf,level)!=0)//�Ѿ������
						error(5);
					else
					{
						enterTable(id,intkind,varkind,level,*address,1,0);//�˴���������һ�����ͣ�����intkind
						(*address)++;
					}
				}
				else 
					error(9);//���������ж��ź���Ӧ�ø�һ����ʶ��
				getSym();
			}
			if(sym==colonsym)//����ð�ţ���Ҫ�Ա����������͸�ֵ
			{
				getSym();
				if(sym==intsym)
					for(i=tx0;i<=tableindex;i++)//�ӿ�ʼ������ǰλ��
						backEnter(i,intkind,varkind,0);//��������
				else if(sym==realsym)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,realkind,varkind,0);
				else if(sym==charsym)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,charkind,varkind,0);
				else if(sym==arraysym)
				{
					getSym();
					if(sym=lbracket)//��������
					{
						getSym();
						if(sym!=intNumber)//����������Ӧ�����޷�������
							error(10);
						getSym();
						if(sym!=rbracket)
							error(11);//ȱ��������
						getSym();
						if(sym==ofsym)//����"of"
						{
							getSym();
							if(sym==intsym)
							{
									backEnter(tx0,intkind,varkind,1);//��������
									Table[tx0].index=arrayindex;
									arrayindex++;
									enterArray(tx0,intkind,INumber);
									*address=Table[tx0].address+INumber;
								for(i=tx0+1;i<=tableindex;i++)//����ǰλ��
								{
									backEnter(i,intkind,varkind,1);//��������
									Table[i].index=arrayindex;
									arrayindex++;
									enterArray(i,intkind,INumber);
									Table[i].address=*address;//��ַҪ��������ĳ���
									*address=Table[i].address+INumber;//��һ�������ĵ�ַ
								}
							}
							else if(sym==realsym)
							{
									backEnter(tx0,realkind,varkind,1);//��������
									Table[tx0].index=arrayindex;
									arrayindex++;
									enterArray(tx0,realkind,INumber);
									*address=Table[tx0].address+INumber;
								for(i=tx0+1;i<=tableindex;i++)//����ǰλ��
								{
									backEnter(i,realkind,varkind,1);//��������
									Table[i].index=arrayindex;
									arrayindex++;
									enterArray(i,realkind,INumber);
									Table[i].address=*address;//��ַҪ��������ĳ���
									*address=Table[i].address+INumber;//��һ�������ĵ�ַ
								}
							}
							else if(sym==charsym)
							{
									backEnter(tx0,charkind,varkind,1);//��������
									Table[tx0].index=arrayindex;
									arrayindex++;
									enterArray(tx0,charkind,INumber);
									*address=Table[tx0].address+INumber;
								for(i=tx0+1;i<=tableindex;i++)//����ǰλ��
								{
									backEnter(i,charkind,varkind,1);//��������
									Table[i].index=arrayindex;
									arrayindex++;
									enterArray(i,charkind,INumber);
									Table[i].address=*address;//��ַҪ��������ĳ���
									*address=Table[i].address+INumber;//��һ�������ĵ�ַ
								}
							}
							else
								error(12);//�����ڵ����ͣ�
						}
					}
					else
						error(11);
				}
			}
			else
				error(40);//�������������
		}
	}
	else
		error(8);

}

/*
 *<�����ײ�>::=procedure<��ʶ��>[<��ʽ������>];
 *<�����ײ�>::=function <��ʶ��>[<��ʽ������>]: <��������>;
 */
int FuncProDeclare(int level,int *address)
{
	int tx0;
	int paraNumber=0;
	varKind returnVal;
	if(sym==funcsym)
	{
		getSym();
		if(sym==identsym)
		{
			if(DeclarePosition(id,level)!=0)
				error(5);
			else
			{	
				enterTable(id,intkind,funckind,level,0,0,0);//�ǼǷ��ű�,�����͹��̲��÷���ƫ��
				tx0=tableindex;//��¼�´�ʱ�������ڷ��ű��е�λ��
				Table[tx0].address=codeindex;
				getSym();
				if(sym==lparen)//�����������
				{
					paraNumber=parameter(level+1,address);
					getSym();
				}
				if(sym==colonsym)//��ð��
					getSym();
					//�жϷ���ֵ������
				if(sym==intsym)
				{
					returnVal=intkind;
					getSym();
				}
				else if(sym=realsym)
				{
					returnVal=realkind;
					getSym();
				}
				else if(sym=charsym)
				{
					returnVal=charkind;
					getSym();
				}
				else
					error(12);
				if(sym!=semicolon)
					error(4);
				Table[tx0].index=funcindex;
				funcindex++;
				enterFunc(tx0,paraNumber,returnVal);//�ǼǺ�������Ϣ������Ҫ���������size�Ĵ�С
			}
		}
		return tx0;
	}
	else if(sym==prosym)    //<�����ײ�>::=procedure<��ʶ��>'('[<��ʽ������>]')';
	{
		getSym();
		if(sym==identsym)
		{
			if(DeclarePosition(id,level)!=0)
				error(5);
			else
			{
				enterTable(id,intkind,prokind,level,0,0,0);//�ǼǷ��ű�,���̲�����ƫ��
				tx0=tableindex;//��¼�´�ʱ�������ڷ��ű��е�λ��
				Table[tx0].address=codeindex;
				getSym();
				if(sym==lparen)//�����������
				{
					paraNumber=parameter(level+1,address);
					getSym();
				}
				if(sym!=semicolon)
					error(4);
				Table[tx0].index=proindex;
				proindex++;
				enterPro(tx0,paraNumber);//�Ժ�Ҫ������̵�size
		}
		return tx0;
	}
	else
		error(13);

	
	}
}

/*<��ʽ������> ::= '('<��ʽ������>{; <��ʽ������>}')'
 *<��ʽ������> ::=   [var]<��ʶ��>{, <��ʶ��>}: <��������>
 <��ʽ������>  ::=   [var]<��ʶ��>{, <��ʶ��>}: <��������>{; <��ʽ������>}
 */
int parameter(int level,int *address)
{
	int tx0,i;
	int paraNum=0;
	int pointerFlag=0;//����ַ���õı��

	if(sym==lparen)
	{
		getSym();
		if(sym==rparen)
		{
			return paraNum;            //������Ϊ��
		}
		if(sym==varsym)//����ַ����
		{
			pointerFlag=1;
			getSym();
		}
		if(sym==identsym)
		{
			if((tx0=DeclarePosition(id,level))!=0)
				error(5);//��ʶ���ض���
			enterTable(id,intkind,parakind,level,*address,0,0);
			tx0=tableindex;
			(*address)++;
			paraNum++;
			getSym();
			while(sym==comma)
			{
				getSym();
				if(sym==identsym)
					if(DeclarePosition(id,level)!=0)
						error(5);//��ʶ���ض���
				enterTable(id,intkind,parakind,level,*address,0,0);
				(*address)++;
				paraNum++;
				getSym();
			}
			if(sym==colonsym)//ð��
			{
				getSym();
				if(sym==charkind)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,charkind,parakind,0);
				else if(sym==realkind)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,realkind,parakind,0);
				else if(sym==intkind)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,intkind,parakind,0);
			}
		}
		if(pointerFlag==1)
			for(i=tx0;i<=tableindex;i++)
				Table[i].AddUse=1;
		pointerFlag=0;
		getSym();
		while(sym==semicolon)
		{
			getSym();
			if(sym==varsym)//����ַ����
			{
				pointerFlag=1;
				getSym();
			}
			if(sym==identsym)
			{
				if((tx0=DeclarePosition(id,level))!=0)
					error(5);//��ʶ���ض���
				enterTable(id,intkind,parakind,level,*address,0,0);
				tx0=tableindex;
				(*address)++;
				paraNum++;
				getSym();
				while(sym==comma)
				{
					getSym();
					if(sym==identsym)
						if(DeclarePosition(id,level)!=0)
							error(5);//��ʶ���ض���
					enterTable(id,intkind,parakind,level,*address,0,0);
					(*address)++;
					paraNum++;
					getSym();
				}
				if(sym==colonsym)//ð��
				{
					getSym();
					if(sym==charkind)
						for(i=tx0;i<=tableindex;i++)
							backEnter(i,charkind,parakind,0);
					else if(realkind)
						for(i=tx0;i<=tableindex;i++)
							backEnter(i,realkind,parakind,0);
					if(pointerFlag==1)//����б�ǣ���ʾҪ����ַ
						for(i=tx0;i<=tableindex;i++)
							Table[i].AddUse=1;
					pointerFlag=0;
				}	
			}
			getSym();
		}
		if(sym!=rparen)
			error(15);//ȱ��С����

		return paraNum;
	}
}

//<���ʽ>::=[+|-]<��>{<�ӷ������><��>}
varKind expression(int level)
{
	varKind returnVal1=intkind,returnVal2=intkind;
	symbol addop;
	if(sym==addsym||sym==subsym)//��һ���ӺŻ��߼���
	{
		addop=sym;
		getSym();
		returnVal1=term(level);
		if(addop==subsym)
			{
				if(returnVal1==charkind)
					error(35);//charǰ�治�ܼӼ���
				else
					generate(Opr,0,1);//ջ����Ԫȡ�������һ��intkind��ʵ������
		}
	}
	else
		returnVal1=term(level);
	while(sym==addsym||sym==subsym)
	{
		addop=sym;
		getSym();
		returnVal2=term(level);
		/*�ں������ɼӼ�����ָ���Ϊ��������ǲ�����׺���ʽ*/
		if(returnVal1==realkind||returnVal2==realkind)
			returnVal1=realkind;
		if(addop==addsym)//���ɼӷ�ָ��
			generate(Opr,0,2);
		else if(addop==subsym)//���ɼ���ָ��
			generate(Opr,0,3);
	}
	return returnVal1;
}

//<��>::=<����>{<�˷������><����>}
varKind term(int level)
{
	symbol mulop;
	varKind returnVal1,returnVal2;
	returnVal1=factor(level);
	while(sym==mulsym||sym==divsym)
	{
		mulop=sym;
		getSym();
		returnVal2=factor(level);
		
		/*�ں������ɳ˳�����ָ���Ϊ��������ǲ�����׺���ʽ*/
		if(mulop==mulsym)
			generate(Opr,0,4);//���ɳ˷���ָ��
		else if(mulop==divsym)//���ɳ���ָ��
		{
			if(returnVal1==realkind||returnVal2==realkind)
				generate(Opr,0,5);
			else
				generate(Opr,0,12);//���������P-code
		}
	}
	return returnVal1;
}

//<����>::=<��ʶ��>|<��ʶ��>'['<���ʽ>']'|<�޷�������>|<�޷���ʵ��>|'('<���ʽ>')'|<�����������>
varKind factor(int level)
{
	int tx;
	varKind returnVal,returnVal1;
	if(sym==identsym)//���������顢��������
	{
		if((tx=StatementPosition(id,level))!=0)//�Ѿ��������Ŀ���ʹ�õı���
		{
			if(Table[tx].kind==varkind||Table[tx].kind==parakind)//�ñ�ʶ���������Ǳ���
			{
				if(Table[tx].arrayFlag!=1)//��������
				{
					if(Table[tx].AddUse==0)
						generate(Lod,level-Table[tx].level,Table[tx].address);
					else
						generate(LDA,level-Table[tx].level,Table[tx].address);
					getSym();
				}
				else//����
				{
					getSym();
					if(sym=lbracket)// ['<���ʽ>']
					{
						getSym();
						returnVal1=expression(level);
//						if(returnVal1!=intkind)
//							error(17);//������������������     ???????????????
//						else 
						{
							generate(Template,0,arrayTable[Table[tx].index].len);//��������ģ��
							generate(LodArray,level-Table[tx].level,Table[tx].address);
						}
						if(sym==rbracket)
							getSym();
						else
							error(11);//ȱ��������

					}
				}
				return Table[tx].type;
			}
			else if(Table[tx].kind==constkind)//�ñ�ʶ�������ǳ���
			{
				if(Table[tx].type==intkind)
					generate(Lit,0,constTable[Table[tx].index].valueI);
				else if(Table[tx].type==charkind)
					generate(Lit,0,constTable[Table[tx].index].valueC);
				else if(Table[tx].type==realkind)
					generate(Lit,0,constTable[Table[tx].index].valueF);
				getSym();
				return Table[tx].type;
				
			}
			else if(Table[tx].kind==funckind)//�ñ�ʶ���Ǻ��������뺯������
			{
				CallFunc(level);
				generate(LodRet,0,0);
				return funcTable[Table[tx].index].ReturnVal;
			}
		}
		else
			error(14);//��ʶ��û�ж���
	}
	else if(sym==intNumber)//�޷�������
	{
		generate(Lit,0,INumber);//integer������װ��ʱֻ�õ�һ��int�Ͳ����������double��char������Ϊ0������
		getSym();
		return intkind;
	}
	else if(sym==floatNumber)//�޷���ʵ��
	{
		generate(Lit,0,FNumber);//real������װ��ʱֻ��double�Ͳ�����int��char������Ϊ0������
		getSym();
		return realkind;
	}
	else if(sym==lparen)//(���ʽ)
	{
		getSym();
		returnVal=expression(level);//������ʽ�ӳ���
		if(sym==rparen)
			getSym();
		else 
			error(15);//ȱ��С����
		return returnVal;
	}
	else
		error(16);//�����г��ֲ��Ϸ��ĳɷ�
}

/*<����> ::=  <���ʽ><��ϵ�����><���ʽ>
 *<��ϵ�����> ::=   <|<=|>|>= |=|<>
 */
void Condition(int level)
{
	symbol operation;
	varKind returnVal1,returnVal2;
	returnVal1=expression(level);
	operation=sym;
	getSym();
	returnVal2=expression(level);
	//�ķ����ò�����׺���ʽ�����Ժ����ɲ�������
	switch(operation)
	{
		//�˴������һ��������ʵ������
	case lss:generate(Opr,0,10);//С��
		break;
	case leq:generate(Opr,0,11);//С�ڵ���
		break;
	case gtr:generate(Opr,0,8);//����
		break;
	case geq:generate(Opr,0,9);//���ڵ���
		break;
	case eql:generate(Opr,0,6);//����
		break;
	case neq:generate(Opr,0,7);//������
		break;
	default:break;
	}
}

//<�������>::= if<����>then<���> | if<����>then<���>else<���>
void SentenceIf(int level)
{
	int cxNotOK,cxOk;
	if(sym==ifsym)
	{
		getSym();
		Condition(level);
		if(sym==thensym)
			getSym();
		else
			error(18);//ȱ��then

		cxNotOK=codeindex;//��¼�´˴���p-codeλ�ã�Ϊ���Ժ����תָ���
		generate(Jpc,0,0);
		Sentence(level);
		if(sym==elsesym)
		{
			cxOk=codeindex;
			generate(Jmp,0,0);
			getSym();
			//����Jpcָ��
			codeTable[cxNotOK].a=codeindex;
			Sentence(level);
			codeTable[cxOk].a=codeindex;//����jmpָ��

		}
		else
			codeTable[cxNotOK].a=codeindex;
	}
}

//<��ֵ���> ::= <��ʶ��> := <���ʽ>|<������ʶ��> := <���ʽ> |<��ʶ��>'['<���ʽ>']':= <���ʽ>
void SentenceAssign(int level)
{
	int tx;
	varKind returnVal1,returnVal2;
	if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))!=0)//�Ѿ������
		{
			returnVal1=Table[tx].type;
			getSym();
			if(sym==becomes)// :=
			{
				getSym();
			
				returnVal2=expression(level);
//				if(returnVal2>returnVal1)
//					printf("Warning:���ڳ�����������͵�ת����\n");
				if(Table[tx].kind==varkind)//����
					generate(Sto,level-Table[tx].level,Table[tx].address);
				else if(Table[tx].kind==parakind)
				{
					if(Table[tx].AddUse==0)
						generate(Sto,level-Table[tx].level,Table[tx].address);
					else if(Table[tx].AddUse==1)
						generate(StoA,level-Table[tx].level,Table[tx].address);
				}
				else if(Table[tx].kind==funckind)//����
					generate(StoRet,0,0);
			}
			else if(sym==lbracket)// [
			{
				getSym();
				returnVal2=expression(level);
//				if(returnVal2!=intkind)
//					error(17);//������������������
				if(sym==rbracket)
					getSym();
				else
					error(11);//ȱ��������
				if(Table[tx].arrayFlag!=1)
					error(21);//��������
				generate(Template,0,arrayTable[Table[tx].index].len);
				if(sym==becomes)
				{
					getSym();
					returnVal2=expression(level);
					if(returnVal2>returnVal1)
						printf("Warning:���ڳ�����������͵�ת����\n");
					generate(StoArray,level-Table[tx].level,Table[tx].address);//���ɱ��������ָ��
				}
		
			}
			else
				error(33);//��ֵ�����ֲ��Ϸ�����
		}
		else
			error(14);//��ʶ��δ����
	}
}

//<�����> ::= read'('<��ʶ��>{,<��ʶ��>}')'
void SentenceRead(int level)
{
	int tx;
	if(sym==readsym)
	{
		getSym();
		if(sym==lparen)
		{
			do{
				getSym();
				if(sym==identsym)
				{
					tx=StatementPosition(id,level);
					if(tx==0)
						error(14);//δ����ı�ʶ��
					else if(Table[tx].kind!=varkind)
						error(31);//������ֻ�ܶԱ�������
					else
					{
						if(Table[tx].type==intkind)
							generate(RedI,level-Table[tx].level,Table[tx].address);
						else if(Table[tx].type==realkind)
							generate(RedR,level-Table[tx].level,Table[tx].address);
						else if(Table[tx].type==charkind)
							generate(RedC,level-Table[tx].level,Table[tx].address);
					}
				}
				else
					error(20);//������в��Ϸ��ɷ�
				getSym();
			}while(sym==comma);
		}
		else
			error(15);//ȱ��С����
		if(sym!=rparen)
			error(15);//ȱ��С����
		getSym();
	}
}

//<�������> ::= begin<���>{;<���>}end
void SentenceBegin(int level)
{
	if(sym==beginsym)
	{
		getSym();
		Sentence(level);
		while(sym==semicolon||sym==beginsym||sym==ifsym||sym==repeatsym||sym==forsym)
		{
			if(sym==semicolon)
				getSym();
			else
				error(4);//û���ԷֺŽ�β
			Sentence(level);
		}
		if(sym==endsym)
			getSym();
		else
			error(22);//ȱ��end
	}
	else
		error(36);//ȱ��begin
}

//<��ѭ�����> ::= while<����>do<���>
void SentenceRepeat(int level)
{
	int cx1,cx2;
	if(sym==repeatsym)
	{
		cx1=codeindex;
		getSym();
		Sentence(level);
		if(sym==untilsym)
		{
			getSym();
			Condition(level);
			cx2=codeindex;
			generate(Jpc,0,0);//�����ɿյ���תָ��Ժ��ڷ���
			generate(Jmp,0,cx1);
			codeTable[cx2].a=codeindex;
		}
		else
			error(43);//ȱ��until
	}
}


//<forѭ�����> ::= for <��ʶ��> := <���ʽ> to <���ʽ>by [+|-] <�޷�������> do <���>
void SentenceFor(int level)
{
	int tx;
	int cx1,cx2;//����������תָ��
	varKind returnVal1,returnVal2;
	int symtmp=17;
	if(sym==forsym)
	{
		getSym();
		if(sym==identsym)
		{
			if((tx=StatementPosition(id,level))!=0)
			{
				if(Table[tx].kind!=varkind||Table[tx].arrayFlag==1)
					error(24);//���Ǳ���
				returnVal1=Table[tx].type;
				//<��ʶ��> := <���ʽ>
				generate(Lod,level-Table[tx].level,Table[tx].address);
				getSym();
				if(sym==becomes)
				{
					getSym();
					returnVal2=expression(level);
					generate(Sto,level-Table[tx].level,Table[tx].address);

				}
				else
					error(34);//ȱ�ٸ�ֵ����
				
				if(sym==tosym||sym==downtosym)
				{
					symtmp=sym;
					generate(Lod,level-Table[tx].level,Table[tx].address);
					if(symtmp==tosym)
					{						
						generate(Lit,0,-1);//����-1,�������������+1�ж�����
						generate(Opr,0,2);//�Ӹ�1
					}
					else
					{
						generate(Lit,0,1);//����1
						generate(Opr,0,2);//��1
					}
					generate(Sto,level-Table[tx].level,Table[tx].address);

					getSym();
					cx1=codeindex;   //ָ��������
					expression(level);
					generate(Lod,level-Table[tx].level,Table[tx].address);
					generate(Lit,0,1);//����1
					if(symtmp==tosym)
						generate(Opr,0,2);//�ӷ�
					else
						generate(Opr,0,3);//����
					generate(Sto,level-Table[tx].level,Table[tx].address);//�����id
					generate(Lod,level-Table[tx].level,Table[tx].address);//��id�ŵ�ջ��
					if(symtmp==tosym)
						generate(Opr,0,9);//����ָ��
					else
						generate(Opr,0,11);//С��ָ��
					cx2=codeindex;
					generate(Jpc,0,0);
				}
				else
					error(42);

				//getSym();
				if(sym==dosym)
					getSym();
				else 
					error(23);//ȱ��do
				Sentence(level);
				generate(Jmp,0,cx1);//����������cx1��
				codeTable[cx2].a=codeindex;//����Jpc��תָ��
				//getSym();
			}
				
		}
		else 
			error(14);//��ʶ��δ����
	}
}

//<д���> ::= write '(' <�ַ���>,<���ʽ> ')'|write'(' <�ַ���> ')'|write'('<���ʽ>')'
void SentenceWrite(int level)
{
	int i=0;
	varKind returnVal;
	if(sym==writesym)
	{
		getSym();
		if(sym==lparen)
		{
			getSym();
			if(sym==stringsym)//�����ַ���
			{
				/*�����ַ�������������ǽ�����ֳ�һ�������ַ�������ջ����Ȼ���ε��ô�ӡָ��*/
				while(buf[i]!='\0')
				{
					generate(Lit,0,buf[i]);
					generate(WrtC,0,0);
					i++;
				}

				getSym();
				if(sym==comma)
				{
					getSym();
					returnVal=expression(level);
					if(returnVal==intkind)
						generate(WrtI,0,0);//��ջ���ı��ʽֵ��ӡ����
					else if(returnVal==realkind)
						generate(WrtR,0,0);
					else if(returnVal==charkind)
						generate(WrtC,0,0);
					
				}
				if(sym!=rparen)
					error(25);//д����г��ֲ��Ϸ��ɷ�
				getSym();
			}
			else
			{
				returnVal=expression(level);
					if(returnVal==intkind)
						generate(WrtI,0,0);//��ջ���ı��ʽֵ��ӡ����
					else if(returnVal==realkind)
						generate(WrtR,0,0);
					else if(returnVal==charkind)
						generate(WrtC,0,0);
				if(sym!=rparen)
					error(15);//ȱ��С����
				getSym();
			}
		}
	}
 }

/*<�����������> ::=  <��ʶ��>[<ʵ�ڲ�����>]                   
*<ʵ�ڲ�����>  ::= '(' <ʵ�ڲ���> {, <ʵ�ڲ���>}')'
*<ʵ�ڲ���>   ::=   <���ʽ>| <��ʶ��>|<�����������>
*/
void CallFunc(int level)
{
	int tx,tx1;
	int paraNum=0;
	varKind returnVal1,returnVal2;
	if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))==0)
			error(14);//��ʶ��δ����
		else
		{
			if(Table[tx].kind!=funckind)
				error(27);//���Ǻ���
			else
			{
				getSym();
				if(sym!=lparen)//���βεĺ���
				{
					error(15);
//					if(funcTable[Table[tx].index].paraNum!=0)
//						error(28);//����������ƥ��
//					else
//						generate(Cal,level-Table[tx].level,Table[tx].address);//���ɵ��ú�����ָ��
				}
				else if(sym==lparen)//��(
				{
					getSym();
					if(sym==rparen)
					{
						generate(Cal,level-Table[tx].level,Table[tx].address);//���ɵ��ú�����ָ��
						getSym();
					}
					else      //�������ĺ�����ֵ����Щ�����
					{
					tx1=StatementPosition(id,level);
					paraNum++;
					if(Table[tx+paraNum].AddUse==1)//����β��Ǵ���ַ����
					{
						getSym();
						if(sym==lbracket)//����
						{
							getSym();
							returnVal2=expression(level);
							if(returnVal2!=intkind)
								error(17);//������������������
							generate(Template,0,arrayTable[Table[tx1].index].len);//��������ģ��
							if(sym==rbracket)
								getSym();
							else
								error(11);//ȱ��������
							if(Table[tx1].arrayFlag!=1)
								error(21);//��������
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
							generate(Opr,0,2);//�ӷ������������ʼ��ַ��ƫ�Ƶ�ַ��ӣ��γɸ���������ľ��Ե�ַ
							generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
							paraT++;

						}
						else if(sym==comma||sym==rparen)
						{
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//�Ѹ�ʵ�εľ��Ե�ַ�ŵ�ջ��
							generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
							paraT++;
						}
						else
							error(37);//����ַ���õ�ʵ��ֻ���Ǳ�ʶ��������Ԫ�أ�
					}
					else
					{
						returnVal1=expression(level);

						if(Table[tx+paraNum].type<returnVal1)
						//	printf("Warning:���ڳ�����������͵�ת����\n");

						/*��ǰջ���Ѿ���expression��ֵ�ˣ�ֱ�����ɱ�����β��е�ָ��*/
						generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ��ֵ���浽paraStackջ��
						paraT++;
					}
					if(sym!=comma&&sym!=rparen)
						error(29);//ʵ���г��ֲ��Ϸ��ɷ�	
					while(sym==comma)
					{
						getSym();
						tx1=StatementPosition(id,level);
						paraNum++;
						if(Table[tx+paraNum].AddUse==1)//����β��Ǵ���ַ����
						{
							getSym();
							if(sym==lbracket)//����
							{
								getSym();
								returnVal2=expression(level);
								if(returnVal2!=intkind)
									error(17);//������������������
								if(sym==rbracket)
									getSym();
								else
									error(11);//ȱ��������
								if(Table[tx1].arrayFlag!=1)
									error(21);//��������
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
								generate(Opr,0,2);//�ӷ������������ʼ��ַ��ƫ�Ƶ�ַ��ӣ��γɸ���������ľ��Ե�ַ
								generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
								paraT++;

							}
							else if(sym==comma||sym==rparen)
							{
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//�Ѹ�ʵ�εľ��Ե�ַ�ŵ�ջ��
								generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
								paraT++;
							}
							else
								error(37);//����ַ���õ�ʵ��ֻ���Ǳ�ʶ��������Ԫ�أ�
						}
						else
						{
							returnVal1=expression(level);

							if(Table[tx+paraNum].type<returnVal1)
								printf("Warning:���ڳ�����������͵�ת����\n");

							/*��ǰջ���Ѿ���expression��ֵ�ˣ�ֱ�����ɱ�����β��е�ָ��*/
							generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ��ֵ���浽paraStackջ��
							paraT++;
						}
		
					}
					if(sym!=rparen)
						error(15);//ȱ��С����
					if(paraNum!=funcTable[Table[tx].index].paraNum)//����������һ��
						error(28);
					generate(AssignPara,0,paraT);
					paraT=0;
					generate(Cal,level-Table[tx].level,Table[tx].address);
					getSym();
					}
				}
			}
		}

	}
}
/*
 *���̵������
*/
void CallPro(int level)
{
	int tx,tx1;
	int paraNum=0;
	varKind returnVal1,returnVal2;
	if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))==0)
			error(14);//��ʶ��δ����
		else
		{
			if(Table[tx].kind!=prokind)
				error(27);//���ǹ���
			else
			{
				getSym();
				if(sym!=lparen)//���βεĹ��̡�����������������
				{
					error(15);
				}
				else if(sym==lparen)//��(
				{

					getSym();
					if(sym==rparen)
					{
						generate(Cal,level-Table[tx].level,Table[tx].address);//���ɵ��ú�����ָ��
						getSym();
					}
					else
					{
					tx1=StatementPosition(id,level);
					paraNum++;
					if(Table[tx+paraNum].AddUse==1)//����β��Ǵ���ַ����
					{
						getSym();
						if(sym==lbracket)//����
						{
							getSym();
							returnVal2=expression(level);
							if(returnVal2!=intkind)
								error(17);//������������������
							if(sym==rbracket)
								getSym();
							else
								error(11);//ȱ��������
							if(Table[tx1].arrayFlag!=1)
								error(21);//��������
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
							generate(Opr,0,2);//�ӷ������������ʼ��ַ��ƫ�Ƶ�ַ��ӣ��γɸ���������ľ��Ե�ַ
							generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
							paraT++;

						}
						else if(sym==comma||sym==rparen)
						{
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//�Ѹ�ʵ�εľ��Ե�ַ�ŵ�ջ��
							generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
							paraT++;
						}
						else
							error(37);//����ַ���õ�ʵ��ֻ���Ǳ�ʶ��������Ԫ�أ�
					}
					else
					{
						returnVal1=expression(level);

						if(Table[tx+paraNum].type<returnVal1)
							printf("Warning:���ڳ�����������͵�ת����\n");

						/*��ǰջ���Ѿ���expression��ֵ�ˣ�ֱ�����ɱ�����β��е�ָ��*/
						generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ��ֵ���浽paraStackջ��
						paraT++;
					}
					while(sym==comma)
					{
						getSym();
						tx1=StatementPosition(id,level);
						paraNum++;
						if(Table[tx+paraNum].AddUse==1)//����β��Ǵ���ַ����
						{
							getSym();
							if(sym==lbracket)//����
							{
								getSym();
								returnVal2=expression(level);
								if(returnVal2!=intkind)
									error(17);//������������������
								if(sym==rbracket)
									getSym();
								else
									error(11);//ȱ��������
								if(Table[tx1].arrayFlag!=1)
									error(21);//��������
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
								generate(Opr,0,2);//�ӷ������������ʼ��ַ��ƫ�Ƶ�ַ��ӣ��γɸ���������ľ��Ե�ַ
								generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
								paraT++;
	
							}
							else if(sym==comma||sym==rparen)
							{
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//�Ѹ�ʵ�εľ��Ե�ַ�ŵ�ջ��
								generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ�ε�ַ���浽paraStackջ��
								paraT++;
							}
							else
								error(37);//����ַ���õ�ʵ��ֻ���Ǳ�ʶ��������Ԫ�أ�
						}
						else
						{
							returnVal1=expression(level);

							if(Table[tx+paraNum].type<returnVal1)
								printf("Warning:���ڳ�����������͵�ת����\n");

							/*��ǰջ���Ѿ���expression��ֵ�ˣ�ֱ�����ɱ�����β��е�ָ��*/
							generate(StoPara,0,0);//StoParaָ��ѵ�ǰջ����ʵ��ֵ���浽paraStackջ��
							paraT++;
						}
						
					}
					if(sym!=rparen)
						error(15);//ȱ��С����
					if(paraNum!=proTable[Table[tx].index].paraNum)//����������һ��
						error(28);
					generate(AssignPara,0,paraT);
					paraT=0;
					generate(Cal,level-Table[tx].level,Table[tx].address);
					getSym();
					}
				}
			}
		}

	}
}

//<���>::=<��ֵ���>|<�������>|<��ѭ�����>|<���̵������>|<�������>|<�����>|<д���>|<forѭ�����>|<��>
void Sentence(int level)
{
	int tx;
	if(sym==ifsym)
		SentenceIf(level);
	else if(sym==repeatsym)
		SentenceRepeat(level);
	else if(sym==beginsym)
		SentenceBegin(level);
	else if(sym==readsym)
		SentenceRead(level);
	else if(sym==writesym)
		SentenceWrite(level);
	else if(sym==forsym)
		SentenceFor(level);
	else if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))==0)
			error(14);//δ����
		else
		{
			if(Table[tx].kind==prokind)
				CallPro(level);
			else 
				SentenceAssign(level);
		}
	}
}
/*����ִ��P-code����*/
void interpret()
{

	int tempI;
	double tempR;
	char tempC;
	int k,buf;
	double FuncReturn;

	t=0;
	b=0;
	p=0;
	for(j=0;j<500;j++)
		s[j]=0;


	do
	{
 		i=codeTable[p];
		p++;
		switch (i.f)
		{
		case Lit:	//ȡ����е�������ʵ�����ַ����߳����ŵ�ջ��
			t++;
			s[t]=i.a;
			break;
		case Opr://�������
			switch((int)(i.a))
		{
		case 0://������һ�����õ�λ��
			t=b-1;
			p=(int)s[t+4];
			b=(int)s[t+2];
			break;
		case 1://ջ����Ԫ��ֵȡ��
			s[t]=-s[t];
			break;
		case 2://�ӷ���ջ���Ӵ�ջ����������ջ����
			t--;
			s[t]=s[t]+s[t+1];
			break;
		case 3:// ��������ջ����ջ����������ջ����
			t--;
			s[t]=s[t]-s[t+1];
			break;
		case 4://�˷�����ջ������ջ����������ջ����
			t--;
			s[t]=s[t]*s[t+1];
			break;
		case 5://��������ջ������ջ����������ջ����
			t--;
			s[t]=s[t]/s[t+1];
			break;
		case 6://�߼����㣺��ȱȽϣ��������0��1��������ջ��
			t--;
			if(s[t]==s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 7://����
			t--;
			if(s[t]!=s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 8://����
			t--;
			if(s[t]>s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 9://���ڵ���
			t--;
			if(s[t]>=s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 10://С��
			t--;
			if(s[t]<s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 11://С�ڵ���
			t--;
			if(s[t]<=s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 12://��������
			t--;
			s[t]=(int)((int)s[t]/(int)s[t+1]);
			break;
		default:
			break;
		}
			break;
		case Lod://�ҵ������ĵ�ַ��������ջ��
			t++;
			s[t]=s[base(i.l)+(int)i.a];
			break;
		case LodArray://��������ĵڼ���Ԫ��
			t++;
			s[t-1]=s[base(i.l)+(int)i.a+(int)s[t-1]];
			t--;
			break;
		case Sto://������ջ�����ݱ��������
			s[base(i.l)+(int)i.a]=s[t];
			t--;
			break;
		case StoArray://������ջ�����ݱ����������ĳ��Ԫ��
			s[base(i.l)+(int)i.a+(int)s[t-1]]=s[t];
			t--;
			break;
		case StoPara://��������ʵ�δ���paraStackջ�������Ժ󱣴浽���¼���βε�λ����
			paraStack[paraT]=s[t];
			paraT++;
			t--;
			break;
		case AssignPara://��paraStackջ�е�ʵ��ֵһһ�������¼���β�λ����
			buf=t+5;
			paraT=0;
			for(k=0;k<(int)i.a;k++)
			{
				s[buf]=paraStack[k];
				buf++;
			}
			break;
		case Cal://���̺�������
			s[t+1]=base(i.l);//��̬��
			s[t+2]=b;//��̬��
			s[t+4]=p;//��������ַ
			b=t+1;
			p=(int)i.a;
			break;
		case Int://����ռ�
			t=t+(int)i.a;
			break;
		case Jmp://��������ת
			p=(int)i.a;
			break;
		case Jpc://��������ת
			if(((int)s[t])==0)
			{
				p=(int)i.a;
				t--;
			}
			break;
		case RedI://����integer������
			scanf("%d",&tempI);
			s[base(i.l)+(int)i.a]=tempI;
			break;
		case RedR://����real������
			scanf("%f",&tempR);
			s[base(i.l)+(int)i.a]=tempR;
			break;
		case RedC://����char������
			scanf("%c",&tempC);
			s[base(i.l)+(int)i.a]=tempC;
			break;
		case WrtI:
			printf("%d",(int)s[t]);
			t++;
			break;
		case WrtR:
			printf("%lf",s[t]);
			t++;
			break;
		case WrtC:
			printf("%c",(char)s[t]);
			t++;
			break;
		case LodRet://�������ķ���ֵ���浽�м����FuncReturn��
			t++;
			s[t]=FuncReturn;
			break;
		case StoRet://�Ѵ���FuncReturn�е�ֵ�ŵ�ջ����������һ���Ĳ���
			FuncReturn=s[t];
			t--;
			break;
		case LodAdd://��ʵ�εĵ�ַ�ŵ�ջ��
			t++;
			s[t]=base(i.l)+(int)i.a;
			break;
		case LDA://���Ѱַ
			t++;
			s[t]=s[(int)s[base(i.l)+(int)(i.a)]];
			break;
		case StoA://��Ӵ�
			s[(int)s[base(i.l)+(int)(i.a)]]=s[t];
			t--;
			break;
		case Template://��������ģ�壬���ж�̬���
			if(s[t]>=i.a||s[t]<0)
			{
				printf("RuntimeError:�����±�Խ�磡\n");
				return;
			}
			break;
		default:
			break;
		}
	}while(p!=0);
}

/*ͨ����̬�����ң���l�Σ�l�ǲ�β�*/
int base(int l)
{
	int b1;
	b1=b;
	while(l>0)
	{
		b1=(int)s[b1];
		l=l-1;
	}
	return b1;
}
/*��ӡ�������е�ָ��*/
void listcode()
{

	int i=0;
	PcodeOut=fopen("P_code_Out.txt","w");
	for(i=0;i<codeindex;i++)
	{
		fprintf(PcodeOut,"%d	",i);
		switch (codeTable[i].f)
		{
		case 0:fprintf(PcodeOut,"Lit  ");
			break;
		case 1:fprintf(PcodeOut,"Opr  ");
			break;
		case 2:fprintf(PcodeOut,"Lod  ");
			break;
		case 3:fprintf(PcodeOut,"Sto  ");
			break;
		case 4:fprintf(PcodeOut,"Cal  ");
			break;
		case 5:fprintf(PcodeOut,"Int  ");
			break;
		case 6:fprintf(PcodeOut,"Jmp  ");
			break;
		case 7:fprintf(PcodeOut,"Jpc  ");
			break;
		case 8:fprintf(PcodeOut,"WrtI  ");
			break;
		case 9:fprintf(PcodeOut,"LodArray  ");
			break;
		case 10:fprintf(PcodeOut,"StoArray  ");
			break;
		case 11:fprintf(PcodeOut,"RedI  ");
			break;
		case 12:fprintf(PcodeOut,"RedR  ");
			break;
		case 13:fprintf(PcodeOut,"RedC  ");
			break;
		case 14:fprintf(PcodeOut,"StoPara   ");
			break;
		case 15:fprintf(PcodeOut,"AssignPara   ");
			break;
		case 16:fprintf(PcodeOut,"WrtR	");
			break;	
		case 17:fprintf(PcodeOut,"WrtC	");
			break;	
		case 18:fprintf(PcodeOut,"LodRet	");
			break;
		case 19:fprintf(PcodeOut,"StoRet	");
			break;
		case 20:fprintf(PcodeOut,"LodAdd	");
			break;
		case 21:fprintf(PcodeOut,"LDA 	");
			break;
		case 22:fprintf(PcodeOut,"StoA	");
			break;
		case 23:fprintf(PcodeOut,"Template	");
			break;
		default:break;
		}
		fprintf(PcodeOut,"%d  %.0lf\n",codeTable[i].l,codeTable[i].a);
	}
	fclose(PcodeOut);
}

/*��ӡ���ű���tableInfo.txt*/
void printTableInfo()
{
	int i;
	tableOut=fopen("TableInfo.txt","w");
	for(i=1;i<=tableindex;i++)
		fprintf(tableOut,"name:%s\t type:%d\t kind:%d\t level:%d\t address:%d\n",Table[i].name,Table[i].type
		,Table[i].kind,Table[i].level,Table[i].address);
	fclose(tableOut);
}
/* <�ֳ���>::=[<����˵������>][<����˵������>]{[<����˵������>]| [<����˵������>]}<�������>*/
void block(int level,int *address)
{
	int cx0=codeindex;
	int tx0;
	int add=4;
	int constFlag=0;//������ǳ��������ͱ����������������������ڱ�������֮ǰ
	generate(Jmp,0,0);//�Ժ���������
	do
	{	
		
		if(sym==constsym)//����ǹؼ���"const"������볣�������ӳ���
		{
			if(constFlag==1)
				error(39);//�������������ڱ�������֮ǰ��
			Constdeclaration(level);
			while(sym==comma)//����������ţ��������һ����������
			{
				Constdeclaration(level);
			}
			if(sym==semicolon)//�ֺţ�������������
				getSym();
			else
			{
				getSym();
				error(4);//������������û���ԷֺŽ���
			}
		}
		if(sym==varsym)
		{
			constFlag=1;
			getSym();
			Vardeclaration(level,address);
			getSym();
			while(sym==semicolon)
			{
				getSym();//����������������Ԥ��һ�����ţ�����Ǳ�ʶ���������������������˵������
				if(sym==identsym)
				{
					Vardeclaration(level,address);
					getSym();
				}
			}
		}
		while(sym==prosym||sym==funcsym)
		{	
			add=4;
			tx0=FuncProDeclare(level,&add);
 			if(sym==semicolon)
				getSym();
			else
				error(4);//û���ԷֺŽ�β
			block(level+1,&add);
			PopTable(tx0+1,tableindex);
			if(sym==semicolon)
				getSym();
			else
				error(4);//û���ԷֺŽ�β
		}
	}while(sym==constsym||sym==varsym||sym==funcsym||sym==prosym);
	codeTable[cx0].a=codeindex;//������ת��ַ
	generate(Int,0,*address);
	SentenceBegin(level);
	generate(Opr,0,0);//return
}


void main()
{
	//��main�����г�ʼ����ռ䣬�ֱ��ǣ�SL��̬����DL��̬������������ֵ��RA���ص�ַ
	int add=4;
	int i;
//	char fileName[40];
	char* fileName=(char*)malloc(sizeof(char)*500); 
	printf("�������������֣�");
	gets(fileName);
	fileIn=fopen(fileName,"r");
	
	getSym();
	block(0,&add);

	if(sym!=period)
		error(32);

	//��ӡ���ű�
	printTableInfo();
	//��ӡP-code
	listcode();
	
	if(errNum==0)
		interpret();
	else
		printf("���ִ���%d ��\n",errNum);

	getchar();

	getchar();
}













