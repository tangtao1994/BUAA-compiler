 #include<stdio.h>
#include"PL0.h"


int enterTable(char *name,varKind type,identKind kind,int level,int address,int arrayFlag,int AddFlag);
void backEnter(int tx,varKind type,identKind kind,int arrayFlag);
void enterConst(varKind type,int Inum,double Fnum,char Cnum);
void enterArray(int tx,varKind type,int len);
void enterFunc(int tx,int Num,varKind ReturnVal);
void enterPro(int tx,int Num);
int DeclarePosition(char *name,int lev);//声明时查表
int StatementPosition(char *name,int lev);//语句部分查表
void printTableInfo();//打印符号表信息到tableInfo.txt


/*******************************词法分析******************************/
int getSym();
int getch();
void error(int index);


/******************************语法分析******************************/
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

/*对于这几个函数，我们利用它们的返回值判断它们的类型*/
varKind factor();
varKind expression();
varKind term();




/************************P-code指令处理部分************************/
void generate(fct funcName,int lev,double add);
void interpret();
void listcode();
int base(int l);



void error(int index)
{
	/*输出错误信息，第几行，第几位，错误类型*/
	printf("ERROR! Line:%d,Pos:%d,%s\n",lx,cc+1,ERROR_MESSAGE[index]);
	errNum++;
}
/*读取一个字符*/
int getch()
{
	int i;

	if(cc==ll)//读取到当前行的结束
	{
		lx++;
		/*判断是否读到文件的结尾*/
		if(fgets(line,MAXLINE,fileIn)==NULL)
		{
			printf("已经读到文件的结尾！\n");
			fclose(fileIn);
			return 0;
		}
		/*把ll和cc都置为0*/
		ll=0;
		cc=0;
		for(i=0;i<MAXLINE;i++)
			if(line[i]=='\0')//char型数组以'\0'结尾
			{
				ll=i;
				break;
			}
	}
	/*若小于等于*/
	if(cc<ll)
		ch=line[cc++];
	return 1;

}

/*取一个symbol，我们规定，每次操作完都预取一个字符ch*/
int getSym()
{
	int k=0,i,reserveFlag=0;//reserveFlag用于标识是否是标识符

	while(ch==' '||ch== '\t'||ch=='\n')//跳去空格和制表符以及换行符
		getch();

	/*标识符或者是保留字*/
	if(isalpha(ch))
	{0
		buf[k++]=ch;
		getch();
		while(isalpha(ch)||isdigit(ch))//标识符中间允许有数字
		{
			buf[k++]=ch;
			getch();
		}
		buf[k]='\0';
		for(i=0;i<RESERVENUM;i++)
			if(strcmp(reservedWord[i],buf)==0)//是保留字
			{
					sym=reservedSym[i];//把sym置为相应的保留字
					reserveFlag=1;
					break;
			}
		if(reserveFlag==0)
			sym=identsym;//把sym置为标识符
		strcpy(id,buf);//把当前的标识符放入id中
		return 1;
	}

	/*是数字*/
	else if(isdigit(ch))
	{
		buf[k++]=ch;
		getch();
		while(isdigit(ch))
		{
			buf[k++]=ch;//把当前读到的字符装入buf数组中
			getch();
		}
		if(ch=='.')//是real型
		{
			buf[k++]=ch;
			getch();
			while(isdigit(ch))
			{
				buf[k++]=ch;
				getch();
			}
			buf[k]='\0';
			FNumber=atof(buf);//把当前的数字放入INumber中
			sym=floatNumber;//把sym置为实数
			
		}
		else//是integer型
		{
			buf[k]='\0';
			INumber=atoi(buf);//把当前的数字放入FNumber中
			sym=intNumber;//把sym置为整数
		}
		return 1;
	}

	/*是字符*/
	else if(ch=='\'')//此处要使用转义字符
	{
		getch();
		if(isdigit(ch)||isalpha(ch))
			buf[k++]=ch;
		else 
		{
			buf[k]='\0';
			error(0);//字符中存在非法符号
			return 0;
		}
		buf[k]='\0';
		getch();
		if(ch!='\'')//如果下一个字符不是单引号
		{
			error(1);
			return 0;
		}
		sym=character;
		getch();//预取一个字符
		return 1;
	}
	/*是字符串*/
	else if(ch=='\"')//此处使用转义字符
	{
		getch();
		while(ch!='\"')//文法规则要求，字符串中可以有数字、字母和空格	while(isdigit(ch)||isalpha(ch)||ch==' ')
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
		}
		if(ch=='\"')//字符串以双引号结尾
		{
			sym=stringsym;
			getch();
			return 1;
		}
		else//出现其他的非法字符
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
		if(ch=='=')//小于等于
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
			sym=leq;
			return 1;
		}
		else if(ch=='>')//不等于
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
			sym=neq;
			return 1;
		}
		else//小于
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
		if(ch=='=')//大于等于
		{
			buf[k++]=ch;
			buf[k]='\0';
			getch();
			sym=geq;
			return 1;
		}
		else//大于
		{
			sym=gtr;
			return 1;
		}
	}
	else if(ch=='=')//等于
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
	error(3);//若是其他情况，则报错！
	return 0;
}
/*生成P-code指令*/
void generate(fct funcName,int lev,double add)
{
	codeTable[codeindex].f=funcName;
	codeTable[codeindex].a=add;
	codeTable[codeindex].l=lev;
	codeindex++;
}
/*登记符号表*/
int enterTable(char *name,varKind type,identKind kind,int level,int address,int arrayFlag,int AddFlag)
{
	tableindex++;
	strcpy(Table[tableindex].name,name);
	Table[tableindex].type=type;
	Table[tableindex].kind=kind;
	Table[tableindex].level=level;
	Table[tableindex].address=address;/* 此处，并非函数的入口，而是函数名字的位置。
									   * 以后如果需要用到函数的入口，那么由函数的第一个参数的位置
									   * 加上函数登记表中该函数的size即可得到
									   */
	Table[tableindex].arrayFlag=arrayFlag;
	Table[tableindex].AddUse=AddFlag;
	if(kind==varsym&&arrayFlag==1)//如果是数组
		Table[tableindex].index=arrayindex;//把arrayindex赋给该符号表项的index属性,用于以后的查找
	else if(kind==constsym)//如果是常量
		Table[tableindex].index=constindex;//把constindex赋给该符号表项的index属性,用于以后的查找
	else if(kind==funcsym)//如果是函数
		Table[tableindex].index=funcindex;//把funcindex赋给该符号表项的index属性,用于以后的查找
	else if(kind==prosym)//如果是过程
		Table[tableindex].index=proindex;//把proindex赋给该符号表项的index属性,用于以后的查找
	return address-1;
}
/*返填符号表，填入类型和种类*/
void backEnter(int tx,varKind type,identKind kind,int arrayFlag)
{
	Table[tx].type=type;
	Table[tx].kind=kind;
	Table[tx].arrayFlag=arrayFlag;
}
/*登记常量符号表*/
void enterConst(varKind type,int Inum,float Fnum,char Cnum)
{
	constTable[constindex].type=type;
	constTable[constindex].valueC=Cnum;
	constTable[constindex].valueI=Inum;
	constTable[constindex].valueF=FNumber;
	constindex++;
}
/*登记数组符号表*/
void enterArray(int tx,varKind type,int len)
{
	Table[tx].type=type;
	arrayTable[Table[tx].index].type=type;
	arrayTable[Table[tx].index].len=len;
}
/*登记函数表*/
void enterFunc(int tx,int Num,varKind ReturnVal)
{
	funcTable[Table[tx].index].paraNum=Num;
	funcTable[Table[tx].index].ReturnVal=ReturnVal;
}
/*登记过程表*/
void enterPro(int tx,int Num)
{
	proTable[Table[tx].index].paraNum=Num;
}
/*过程函数结束后，将局部变量弹出符号栈*/
void PopTable(int begin,int end)
{
	int i;
	for(i=begin;i<=end;i++)
		Table[i].level=-1;
}

int DeclarePosition(char *name,int lev)//声明时查找字符表中的位置
{
	int i;
	for(i=tableindex;i>0;i--)//从符号表的后面向前面查
	{
		if(strcmp(name,Table[i].name)==0&&lev==Table[i].level)
			return i;
	}
	return 0;//没有找到
}

int StatementPosition(char *name,int lev)//语句部分查找字符表中的位置，可以调用比当前层次低的标识符
{
	int i;
	for(i=tableindex;i>0;i--)
	{
		if(strcmp(name,Table[i].name)==0&&lev>=Table[i].level&&Table[i].level!=-1)
			return i;
	}
	return 0;
}



/* 常量定义ok
 *<常量定义>::=<标识符>＝[+| -] (<无符号整数>| <无符号实数>)|<字符>
 */
void Constdeclaration(int level)
{
	getSym();
	if(sym==identsym)
	{
		if(DeclarePosition(buf,level)!=0)//已经定义过
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
						enterTable(id,intkind,constkind,level,0,0,0);//登记符号表，填入名字，类型，种类，层次，地址，是否是数组
						Table[tableindex].index=constindex;
						enterConst(intkind,INumber,0.0,' ');
					}
					else if(sym==floatNumber)
					{
						enterTable(id,realkind,constkind,level,0,0,0);//登记符号表，填入名字，类型，种类，层次，地址，是否是数组
						Table[tableindex].index=constindex;
						enterConst(realkind,0,FNumber,' ');
					}
				}
				else if(sym==subsym)
				{
					getSym();
					if(sym==intNumber)
					{
						INumber=-INumber;//负号开头，数字取反
						enterTable(id,intkind,constkind,level,0,0,0);//登记符号表，填入名字，类型，种类，层次，地址，是否是数组
						Table[tableindex].index=constindex;
						enterConst(intkind,INumber,0.0,' ');
					}
					else if(sym==floatNumber)
					{
						FNumber=-FNumber;
						enterTable(id,realkind,constkind,level,0,0,0);//登记符号表，填入名字，类型，种类，层次，地址，是否是数组
						Table[tableindex].index=constindex;
						enterConst(realkind,0,FNumber,' ');
					}
				}
				else if(sym==intNumber)
				{
					enterTable(id,intkind,constkind,level,0,0,0);//登记符号表，填入名字，类型，种类，层次，地址，是否是数组	
					Table[tableindex].index=constindex;
					enterConst(intkind,INumber,0.0,' ');
				}
				else if(sym==floatNumber)
				{
					enterTable(id,realkind,constkind,level,0,0,0);//登记符号表，填入名字，类型，种类，层次，地址，是否是数组	
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
					error(6);//常量定义中出现不合法成分！
				}
			}
			else
				error(7);//缺少等号
		}
	}
	else 
	{
		error(8);//不是标识符或者标识符中存在不合法符号
	}
	getSym();
	return ;
}

/* 变量说明
 *<变量说明>::=<标识符>{,<标识符>}:<类型>
 *
 *<类型>::=<基本类型>|array'['<无符号整数>']' of <基本类型>
 */
void Vardeclaration(int level,int *address)
{
	int i,tx0;//因为一种类型的变量可能有很多，所以我们用tx0记录最开始的变量的tableindex值，用于后面的返填类型
	if(sym==identsym)
	{
		if(DeclarePosition(buf,level)!=0)//已经定义过
			error(5);
		else
		{
			enterTable(id,intkind,varkind,level,*address,1,0);//此处先随意填一种类型，比如intkind
			tx0=tableindex;
			(*address)++;
			getSym();
			while(sym==comma)
			{
				getSym();
				if(sym==identsym)
				{
					if(DeclarePosition(buf,level)!=0)//已经定义过
						error(5);
					else
					{
						enterTable(id,intkind,varkind,level,*address,1,0);//此处先随意填一种类型，比如intkind
						(*address)++;
					}
				}
				else 
					error(9);//变量定义中逗号后面应该跟一个标识符
				getSym();
			}
			if(sym==colonsym)//遇到冒号，将要对变量进行类型赋值
			{
				getSym();
				if(sym==intsym)
					for(i=tx0;i<=tableindex;i++)//从开始出到当前位置
						backEnter(i,intkind,varkind,0);//返填类型
				else if(sym==realsym)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,realkind,varkind,0);
				else if(sym==charsym)
					for(i=tx0;i<=tableindex;i++)
						backEnter(i,charkind,varkind,0);
				else if(sym==arraysym)
				{
					getSym();
					if(sym=lbracket)//左中括号
					{
						getSym();
						if(sym!=intNumber)//中括号里面应该是无符号整数
							error(10);
						getSym();
						if(sym!=rbracket)
							error(11);//缺少中括号
						getSym();
						if(sym==ofsym)//遇到"of"
						{
							getSym();
							if(sym==intsym)
							{
									backEnter(tx0,intkind,varkind,1);//返填类型
									Table[tx0].index=arrayindex;
									arrayindex++;
									enterArray(tx0,intkind,INumber);
									*address=Table[tx0].address+INumber;
								for(i=tx0+1;i<=tableindex;i++)//到当前位置
								{
									backEnter(i,intkind,varkind,1);//返填类型
									Table[i].index=arrayindex;
									arrayindex++;
									enterArray(i,intkind,INumber);
									Table[i].address=*address;//地址要加上数组的长度
									*address=Table[i].address+INumber;//下一个变量的地址
								}
							}
							else if(sym==realsym)
							{
									backEnter(tx0,realkind,varkind,1);//返填类型
									Table[tx0].index=arrayindex;
									arrayindex++;
									enterArray(tx0,realkind,INumber);
									*address=Table[tx0].address+INumber;
								for(i=tx0+1;i<=tableindex;i++)//到当前位置
								{
									backEnter(i,realkind,varkind,1);//返填类型
									Table[i].index=arrayindex;
									arrayindex++;
									enterArray(i,realkind,INumber);
									Table[i].address=*address;//地址要加上数组的长度
									*address=Table[i].address+INumber;//下一个变量的地址
								}
							}
							else if(sym==charsym)
							{
									backEnter(tx0,charkind,varkind,1);//返填类型
									Table[tx0].index=arrayindex;
									arrayindex++;
									enterArray(tx0,charkind,INumber);
									*address=Table[tx0].address+INumber;
								for(i=tx0+1;i<=tableindex;i++)//到当前位置
								{
									backEnter(i,charkind,varkind,1);//返填类型
									Table[i].index=arrayindex;
									arrayindex++;
									enterArray(i,charkind,INumber);
									Table[i].address=*address;//地址要加上数组的长度
									*address=Table[i].address+INumber;//下一个变量的地址
								}
							}
							else
								error(12);//不存在的类型！
						}
					}
					else
						error(11);
				}
			}
			else
				error(40);//错误的数据类型
		}
	}
	else
		error(8);

}

/*
 *<过程首部>::=procedure<标识符>[<形式参数表>];
 *<函数首部>::=function <标识符>[<形式参数表>]: <基本类型>;
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
				enterTable(id,intkind,funckind,level,0,0,0);//登记符号表,函数和过程不用分配偏移
				tx0=tableindex;//记录下此时函数名在符号表中的位置
				Table[tx0].address=codeindex;
				getSym();
				if(sym==lparen)//如果有左括号
				{
					paraNumber=parameter(level+1,address);
					getSym();
				}
				if(sym==colonsym)//是冒号
					getSym();
					//判断返回值的类型
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
				enterFunc(tx0,paraNumber,returnVal);//登记函数表信息，后面要返填函数表中size的大小
			}
		}
		return tx0;
	}
	else if(sym==prosym)    //<过程首部>::=procedure<标识符>'('[<形式参数表>]')';
	{
		getSym();
		if(sym==identsym)
		{
			if(DeclarePosition(id,level)!=0)
				error(5);
			else
			{
				enterTable(id,intkind,prokind,level,0,0,0);//登记符号表,过程不分配偏移
				tx0=tableindex;//记录下此时过程名在符号表中的位置
				Table[tx0].address=codeindex;
				getSym();
				if(sym==lparen)//如果有左括号
				{
					paraNumber=parameter(level+1,address);
					getSym();
				}
				if(sym!=semicolon)
					error(4);
				Table[tx0].index=proindex;
				proindex++;
				enterPro(tx0,paraNumber);//以后要返填过程的size
		}
		return tx0;
	}
	else
		error(13);

	
	}
}

/*<形式参数表> ::= '('<形式参数段>{; <形式参数段>}')'
 *<形式参数段> ::=   [var]<标识符>{, <标识符>}: <基本类型>
 <形式参数表>  ::=   [var]<标识符>{, <标识符>}: <基本类型>{; <形式参数表>}
 */
int parameter(int level,int *address)
{
	int tx0,i;
	int paraNum=0;
	int pointerFlag=0;//传地址调用的标记

	if(sym==lparen)
	{
		getSym();
		if(sym==rparen)
		{
			return paraNum;            //括号中为空
		}
		if(sym==varsym)//传地址调用
		{
			pointerFlag=1;
			getSym();
		}
		if(sym==identsym)
		{
			if((tx0=DeclarePosition(id,level))!=0)
				error(5);//标识符重定义
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
						error(5);//标识符重定义
				enterTable(id,intkind,parakind,level,*address,0,0);
				(*address)++;
				paraNum++;
				getSym();
			}
			if(sym==colonsym)//冒号
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
			if(sym==varsym)//传地址调用
			{
				pointerFlag=1;
				getSym();
			}
			if(sym==identsym)
			{
				if((tx0=DeclarePosition(id,level))!=0)
					error(5);//标识符重定义
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
							error(5);//标识符重定义
					enterTable(id,intkind,parakind,level,*address,0,0);
					(*address)++;
					paraNum++;
					getSym();
				}
				if(sym==colonsym)//冒号
				{
					getSym();
					if(sym==charkind)
						for(i=tx0;i<=tableindex;i++)
							backEnter(i,charkind,parakind,0);
					else if(realkind)
						for(i=tx0;i<=tableindex;i++)
							backEnter(i,realkind,parakind,0);
					if(pointerFlag==1)//如果有标记，表示要传地址
						for(i=tx0;i<=tableindex;i++)
							Table[i].AddUse=1;
					pointerFlag=0;
				}	
			}
			getSym();
		}
		if(sym!=rparen)
			error(15);//缺少小括号

		return paraNum;
	}
}

//<表达式>::=[+|-]<项>{<加法运算符><项>}
varKind expression(int level)
{
	varKind returnVal1=intkind,returnVal2=intkind;
	symbol addop;
	if(sym==addsym||sym==subsym)//有一个加号或者减号
	{
		addop=sym;
		getSym();
		returnVal1=term(level);
		if(addop==subsym)
			{
				if(returnVal1==charkind)
					error(35);//char前面不能加减号
				else
					generate(Opr,0,1);//栈顶单元取反，最后一个intkind无实际意义
		}
	}
	else
		returnVal1=term(level);
	while(sym==addsym||sym==subsym)
	{
		addop=sym;
		getSym();
		returnVal2=term(level);
		/*在后面生成加减操作指令，因为所定义的是波兰后缀表达式*/
		if(returnVal1==realkind||returnVal2==realkind)
			returnVal1=realkind;
		if(addop==addsym)//生成加法指令
			generate(Opr,0,2);
		else if(addop==subsym)//生成减法指令
			generate(Opr,0,3);
	}
	return returnVal1;
}

//<项>::=<因子>{<乘法运算符><因子>}
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
		
		/*在后面生成乘除操作指令，因为所定义的是波兰后缀表达式*/
		if(mulop==mulsym)
			generate(Opr,0,4);//生成乘法的指令
		else if(mulop==divsym)//生成除法指令
		{
			if(returnVal1==realkind||returnVal2==realkind)
				generate(Opr,0,5);
			else
				generate(Opr,0,12);//整数相除的P-code
		}
	}
	return returnVal1;
}

//<因子>::=<标识符>|<标识符>'['<表达式>']'|<无符号整数>|<无符号实数>|'('<表达式>')'|<函数调用语句>
varKind factor(int level)
{
	int tx;
	varKind returnVal,returnVal1;
	if(sym==identsym)//变量、数组、函数调用
	{
		if((tx=StatementPosition(id,level))!=0)//已经声明过的可以使用的变量
		{
			if(Table[tx].kind==varkind||Table[tx].kind==parakind)//该标识符的类型是变量
			{
				if(Table[tx].arrayFlag!=1)//不是数组
				{
					if(Table[tx].AddUse==0)
						generate(Lod,level-Table[tx].level,Table[tx].address);
					else
						generate(LDA,level-Table[tx].level,Table[tx].address);
					getSym();
				}
				else//数组
				{
					getSym();
					if(sym=lbracket)// ['<表达式>']
					{
						getSym();
						returnVal1=expression(level);
//						if(returnVal1!=intkind)
//							error(17);//数组索引必须是整数     ???????????????
//						else 
						{
							generate(Template,0,arrayTable[Table[tx].index].len);//载入数组模板
							generate(LodArray,level-Table[tx].level,Table[tx].address);
						}
						if(sym==rbracket)
							getSym();
						else
							error(11);//缺少中括号

					}
				}
				return Table[tx].type;
			}
			else if(Table[tx].kind==constkind)//该标识符类型是常量
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
			else if(Table[tx].kind==funckind)//该标识符是函数，进入函数调用
			{
				CallFunc(level);
				generate(LodRet,0,0);
				return funcTable[Table[tx].index].ReturnVal;
			}
		}
		else
			error(14);//标识符没有定义
	}
	else if(sym==intNumber)//无符号整数
	{
		generate(Lit,0,INumber);//integer型数，装载时只用第一个int型参数，后面的double和char参数置为0，无用
		getSym();
		return intkind;
	}
	else if(sym==floatNumber)//无符号实数
	{
		generate(Lit,0,FNumber);//real型数，装载时只用double型参数，int和char参数置为0，无用
		getSym();
		return realkind;
	}
	else if(sym==lparen)//(表达式)
	{
		getSym();
		returnVal=expression(level);//进入表达式子程序
		if(sym==rparen)
			getSym();
		else 
			error(15);//缺少小括号
		return returnVal;
	}
	else
		error(16);//因子中出现不合法的成分
}

/*<条件> ::=  <表达式><关系运算符><表达式>
 *<关系运算符> ::=   <|<=|>|>= |=|<>
 */
void Condition(int level)
{
	symbol operation;
	varKind returnVal1,returnVal2;
	returnVal1=expression(level);
	operation=sym;
	getSym();
	returnVal2=expression(level);
	//文法中用波兰后缀表达式，所以后生成操作代码
	switch(operation)
	{
		//此处的最后一个参数无实际意义
	case lss:generate(Opr,0,10);//小于
		break;
	case leq:generate(Opr,0,11);//小于等于
		break;
	case gtr:generate(Opr,0,8);//大于
		break;
	case geq:generate(Opr,0,9);//大于等于
		break;
	case eql:generate(Opr,0,6);//等于
		break;
	case neq:generate(Opr,0,7);//不等于
		break;
	default:break;
	}
}

//<条件语句>::= if<条件>then<语句> | if<条件>then<语句>else<语句>
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
			error(18);//缺少then

		cxNotOK=codeindex;//记录下此处的p-code位置，为了以后的跳转指令返填
		generate(Jpc,0,0);
		Sentence(level);
		if(sym==elsesym)
		{
			cxOk=codeindex;
			generate(Jmp,0,0);
			getSym();
			//返填Jpc指令
			codeTable[cxNotOK].a=codeindex;
			Sentence(level);
			codeTable[cxOk].a=codeindex;//返填jmp指令

		}
		else
			codeTable[cxNotOK].a=codeindex;
	}
}

//<赋值语句> ::= <标识符> := <表达式>|<函数标识符> := <表达式> |<标识符>'['<表达式>']':= <表达式>
void SentenceAssign(int level)
{
	int tx;
	varKind returnVal1,returnVal2;
	if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))!=0)//已经定义过
		{
			returnVal1=Table[tx].type;
			getSym();
			if(sym==becomes)// :=
			{
				getSym();
			
				returnVal2=expression(level);
//				if(returnVal2>returnVal1)
//					printf("Warning:存在长类型向短类型的转换！\n");
				if(Table[tx].kind==varkind)//变量
					generate(Sto,level-Table[tx].level,Table[tx].address);
				else if(Table[tx].kind==parakind)
				{
					if(Table[tx].AddUse==0)
						generate(Sto,level-Table[tx].level,Table[tx].address);
					else if(Table[tx].AddUse==1)
						generate(StoA,level-Table[tx].level,Table[tx].address);
				}
				else if(Table[tx].kind==funckind)//函数
					generate(StoRet,0,0);
			}
			else if(sym==lbracket)// [
			{
				getSym();
				returnVal2=expression(level);
//				if(returnVal2!=intkind)
//					error(17);//数组索引必须是整型
				if(sym==rbracket)
					getSym();
				else
					error(11);//缺少中括号
				if(Table[tx].arrayFlag!=1)
					error(21);//不是数组
				generate(Template,0,arrayTable[Table[tx].index].len);
				if(sym==becomes)
				{
					getSym();
					returnVal2=expression(level);
					if(returnVal2>returnVal1)
						printf("Warning:存在长类型向短类型的转换！\n");
					generate(StoArray,level-Table[tx].level,Table[tx].address);//生成保存数组的指令
				}
		
			}
			else
				error(33);//赋值语句出现不合法部分
		}
		else
			error(14);//标识符未定义
	}
}

//<读语句> ::= read'('<标识符>{,<标识符>}')'
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
						error(14);//未定义的标识符
					else if(Table[tx].kind!=varkind)
						error(31);//读操作只能对变量进行
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
					error(20);//读语句中不合法成分
				getSym();
			}while(sym==comma);
		}
		else
			error(15);//缺少小括号
		if(sym!=rparen)
			error(15);//缺少小括号
		getSym();
	}
}

//<复合语句> ::= begin<语句>{;<语句>}end
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
				error(4);//没有以分号结尾
			Sentence(level);
		}
		if(sym==endsym)
			getSym();
		else
			error(22);//缺少end
	}
	else
		error(36);//缺少begin
}

//<当循环语句> ::= while<条件>do<语句>
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
			generate(Jpc,0,0);//先生成空的跳转指令，以后在返填
			generate(Jmp,0,cx1);
			codeTable[cx2].a=codeindex;
		}
		else
			error(43);//缺少until
	}
}


//<for循环语句> ::= for <标识符> := <表达式> to <表达式>by [+|-] <无符号整数> do <语句>
void SentenceFor(int level)
{
	int tx;
	int cx1,cx2;//用来返填跳转指令
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
					error(24);//不是变量
				returnVal1=Table[tx].type;
				//<标识符> := <表达式>
				generate(Lod,level-Table[tx].level,Table[tx].address);
				getSym();
				if(sym==becomes)
				{
					getSym();
					returnVal2=expression(level);
					generate(Sto,level-Table[tx].level,Table[tx].address);

				}
				else
					error(34);//缺少赋值符号
				
				if(sym==tosym||sym==downtosym)
				{
					symtmp=sym;
					generate(Lod,level-Table[tx].level,Table[tx].address);
					if(symtmp==tosym)
					{						
						generate(Lit,0,-1);//载入-1,方便我们下面的+1判定操作
						generate(Opr,0,2);//加负1
					}
					else
					{
						generate(Lit,0,1);//载入1
						generate(Opr,0,2);//加1
					}
					generate(Sto,level-Table[tx].level,Table[tx].address);

					getSym();
					cx1=codeindex;   //指令表的索引
					expression(level);
					generate(Lod,level-Table[tx].level,Table[tx].address);
					generate(Lit,0,1);//载入1
					if(symtmp==tosym)
						generate(Opr,0,2);//加法
					else
						generate(Opr,0,3);//减法
					generate(Sto,level-Table[tx].level,Table[tx].address);//保存回id
					generate(Lod,level-Table[tx].level,Table[tx].address);//把id放到栈顶
					if(symtmp==tosym)
						generate(Opr,0,9);//大于指令
					else
						generate(Opr,0,11);//小于指令
					cx2=codeindex;
					generate(Jpc,0,0);
				}
				else
					error(42);

				//getSym();
				if(sym==dosym)
					getSym();
				else 
					error(23);//缺少do
				Sentence(level);
				generate(Jmp,0,cx1);//无条件跳回cx1处
				codeTable[cx2].a=codeindex;//返填Jpc跳转指令
				//getSym();
			}
				
		}
		else 
			error(14);//标识符未定义
	}
}

//<写语句> ::= write '(' <字符串>,<表达式> ')'|write'(' <字符串> ')'|write'('<表达式>')'
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
			if(sym==stringsym)//读到字符串
			{
				/*对于字符串的输出，我们将它拆分成一个个的字符，放在栈顶，然后多次调用打印指令*/
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
						generate(WrtI,0,0);//把栈顶的表达式值打印出来
					else if(returnVal==realkind)
						generate(WrtR,0,0);
					else if(returnVal==charkind)
						generate(WrtC,0,0);
					
				}
				if(sym!=rparen)
					error(25);//写语句中出现不合法成分
				getSym();
			}
			else
			{
				returnVal=expression(level);
					if(returnVal==intkind)
						generate(WrtI,0,0);//把栈顶的表达式值打印出来
					else if(returnVal==realkind)
						generate(WrtR,0,0);
					else if(returnVal==charkind)
						generate(WrtC,0,0);
				if(sym!=rparen)
					error(15);//缺少小括号
				getSym();
			}
		}
	}
 }

/*<函数调用语句> ::=  <标识符>[<实在参数表>]                   
*<实在参数表>  ::= '(' <实在参数> {, <实在参数>}')'
*<实在参数>   ::=   <表达式>| <标识符>|<函数调用语句>
*/
void CallFunc(int level)
{
	int tx,tx1;
	int paraNum=0;
	varKind returnVal1,returnVal2;
	if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))==0)
			error(14);//标识符未定义
		else
		{
			if(Table[tx].kind!=funckind)
				error(27);//不是函数
			else
			{
				getSym();
				if(sym!=lparen)//无形参的函数
				{
					error(15);
//					if(funcTable[Table[tx].index].paraNum!=0)
//						error(28);//参数个数不匹配
//					else
//						generate(Cal,level-Table[tx].level,Table[tx].address);//生成调用函数的指令
				}
				else if(sym==lparen)//有(
				{
					getSym();
					if(sym==rparen)
					{
						generate(Cal,level-Table[tx].level,Table[tx].address);//生成调用函数的指令
						getSym();
					}
					else      //带参数的函数传值是有些问题的
					{
					tx1=StatementPosition(id,level);
					paraNum++;
					if(Table[tx+paraNum].AddUse==1)//这个形参是传地址调用
					{
						getSym();
						if(sym==lbracket)//数组
						{
							getSym();
							returnVal2=expression(level);
							if(returnVal2!=intkind)
								error(17);//数组索引必须是整型
							generate(Template,0,arrayTable[Table[tx1].index].len);//载入数组模板
							if(sym==rbracket)
								getSym();
							else
								error(11);//缺少中括号
							if(Table[tx1].arrayFlag!=1)
								error(21);//不是数组
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
							generate(Opr,0,2);//加法，把数组的起始地址和偏移地址相加，形成该数组变量的绝对地址
							generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
							paraT++;

						}
						else if(sym==comma||sym==rparen)
						{
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//把该实参的绝对地址放到栈顶
							generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
							paraT++;
						}
						else
							error(37);//传地址调用的实参只能是标识符或数组元素！
					}
					else
					{
						returnVal1=expression(level);

						if(Table[tx+paraNum].type<returnVal1)
						//	printf("Warning:存在长类型向短类型的转换！\n");

						/*当前栈顶已经是expression的值了，直接生成保存回形参中的指令*/
						generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参值保存到paraStack栈中
						paraT++;
					}
					if(sym!=comma&&sym!=rparen)
						error(29);//实参中出现不合法成分	
					while(sym==comma)
					{
						getSym();
						tx1=StatementPosition(id,level);
						paraNum++;
						if(Table[tx+paraNum].AddUse==1)//这个形参是传地址调用
						{
							getSym();
							if(sym==lbracket)//数组
							{
								getSym();
								returnVal2=expression(level);
								if(returnVal2!=intkind)
									error(17);//数组索引必须是整型
								if(sym==rbracket)
									getSym();
								else
									error(11);//缺少中括号
								if(Table[tx1].arrayFlag!=1)
									error(21);//不是数组
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
								generate(Opr,0,2);//加法，把数组的起始地址和偏移地址相加，形成该数组变量的绝对地址
								generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
								paraT++;

							}
							else if(sym==comma||sym==rparen)
							{
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//把该实参的绝对地址放到栈顶
								generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
								paraT++;
							}
							else
								error(37);//传地址调用的实参只能是标识符或数组元素！
						}
						else
						{
							returnVal1=expression(level);

							if(Table[tx+paraNum].type<returnVal1)
								printf("Warning:存在长类型向短类型的转换！\n");

							/*当前栈顶已经是expression的值了，直接生成保存回形参中的指令*/
							generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参值保存到paraStack栈中
							paraT++;
						}
		
					}
					if(sym!=rparen)
						error(15);//缺少小括号
					if(paraNum!=funcTable[Table[tx].index].paraNum)//参数个数不一致
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
 *过程调用语句
*/
void CallPro(int level)
{
	int tx,tx1;
	int paraNum=0;
	varKind returnVal1,returnVal2;
	if(sym==identsym)
	{
		if((tx=StatementPosition(id,level))==0)
			error(14);//标识符未定义
		else
		{
			if(Table[tx].kind!=prokind)
				error(27);//不是过程
			else
			{
				getSym();
				if(sym!=lparen)//无形参的过程。。。。。。。。。
				{
					error(15);
				}
				else if(sym==lparen)//有(
				{

					getSym();
					if(sym==rparen)
					{
						generate(Cal,level-Table[tx].level,Table[tx].address);//生成调用函数的指令
						getSym();
					}
					else
					{
					tx1=StatementPosition(id,level);
					paraNum++;
					if(Table[tx+paraNum].AddUse==1)//这个形参是传地址调用
					{
						getSym();
						if(sym==lbracket)//数组
						{
							getSym();
							returnVal2=expression(level);
							if(returnVal2!=intkind)
								error(17);//数组索引必须是整型
							if(sym==rbracket)
								getSym();
							else
								error(11);//缺少中括号
							if(Table[tx1].arrayFlag!=1)
								error(21);//不是数组
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
							generate(Opr,0,2);//加法，把数组的起始地址和偏移地址相加，形成该数组变量的绝对地址
							generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
							paraT++;

						}
						else if(sym==comma||sym==rparen)
						{
							generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//把该实参的绝对地址放到栈顶
							generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
							paraT++;
						}
						else
							error(37);//传地址调用的实参只能是标识符或数组元素！
					}
					else
					{
						returnVal1=expression(level);

						if(Table[tx+paraNum].type<returnVal1)
							printf("Warning:存在长类型向短类型的转换！\n");

						/*当前栈顶已经是expression的值了，直接生成保存回形参中的指令*/
						generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参值保存到paraStack栈中
						paraT++;
					}
					while(sym==comma)
					{
						getSym();
						tx1=StatementPosition(id,level);
						paraNum++;
						if(Table[tx+paraNum].AddUse==1)//这个形参是传地址调用
						{
							getSym();
							if(sym==lbracket)//数组
							{
								getSym();
								returnVal2=expression(level);
								if(returnVal2!=intkind)
									error(17);//数组索引必须是整型
								if(sym==rbracket)
									getSym();
								else
									error(11);//缺少中括号
								if(Table[tx1].arrayFlag!=1)
									error(21);//不是数组
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);
								generate(Opr,0,2);//加法，把数组的起始地址和偏移地址相加，形成该数组变量的绝对地址
								generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
								paraT++;
	
							}
							else if(sym==comma||sym==rparen)
							{
								generate(LodAdd,level-Table[tx1].level,Table[tx1].address);//把该实参的绝对地址放到栈顶
								generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参地址保存到paraStack栈中
								paraT++;
							}
							else
								error(37);//传地址调用的实参只能是标识符或数组元素！
						}
						else
						{
							returnVal1=expression(level);

							if(Table[tx+paraNum].type<returnVal1)
								printf("Warning:存在长类型向短类型的转换！\n");

							/*当前栈顶已经是expression的值了，直接生成保存回形参中的指令*/
							generate(StoPara,0,0);//StoPara指令，把当前栈顶的实参值保存到paraStack栈中
							paraT++;
						}
						
					}
					if(sym!=rparen)
						error(15);//缺少小括号
					if(paraNum!=proTable[Table[tx].index].paraNum)//参数个数不一致
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

//<语句>::=<赋值语句>|<条件语句>|<当循环语句>|<过程调用语句>|<复合语句>|<读语句>|<写语句>|<for循环语句>|<空>
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
			error(14);//未定义
		else
		{
			if(Table[tx].kind==prokind)
				CallPro(level);
			else 
				SentenceAssign(level);
		}
	}
}
/*解释执行P-code代码*/
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
		case Lit:	//取语句中的整数、实数、字符或者常量放到栈顶
			t++;
			s[t]=i.a;
			break;
		case Opr://运算操作
			switch((int)(i.a))
		{
		case 0://返回上一个调用的位置
			t=b-1;
			p=(int)s[t+4];
			b=(int)s[t+2];
			break;
		case 1://栈顶单元的值取反
			s[t]=-s[t];
			break;
		case 2://加法（栈顶加次栈顶，保存至栈顶）
			t--;
			s[t]=s[t]+s[t+1];
			break;
		case 3:// 减法（次栈顶减栈顶，保存至栈顶）
			t--;
			s[t]=s[t]-s[t+1];
			break;
		case 4://乘法（次栈顶乘以栈顶，保存至栈顶）
			t--;
			s[t]=s[t]*s[t+1];
			break;
		case 5://除法（次栈顶除以栈顶，保存至栈顶）
			t--;
			s[t]=s[t]/s[t+1];
			break;
		case 6://逻辑运算：相等比较，将结果（0或1）保存至栈顶
			t--;
			if(s[t]==s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 7://不等
			t--;
			if(s[t]!=s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 8://大于
			t--;
			if(s[t]>s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 9://大于等于
			t--;
			if(s[t]>=s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 10://小于
			t--;
			if(s[t]<s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 11://小于等于
			t--;
			if(s[t]<=s[t+1])
				s[t]=1;
			else
				s[t]=0;
			break;
		case 12://整数除法
			t--;
			s[t]=(int)((int)s[t]/(int)s[t+1]);
			break;
		default:
			break;
		}
			break;
		case Lod://找到变量的地址，并存入栈顶
			t++;
			s[t]=s[base(i.l)+(int)i.a];
			break;
		case LodArray://载入数组的第几个元素
			t++;
			s[t-1]=s[base(i.l)+(int)i.a+(int)s[t-1]];
			t--;
			break;
		case Sto://将数据栈顶内容保存入变量
			s[base(i.l)+(int)i.a]=s[t];
			t--;
			break;
		case StoArray://将数据栈顶内容保存至数组的某个元素
			s[base(i.l)+(int)i.a+(int)s[t-1]]=s[t];
			t--;
			break;
		case StoPara://将函数的实参存入paraStack栈，用于以后保存到活动记录的形参的位置上
			paraStack[paraT]=s[t];
			paraT++;
			t--;
			break;
		case AssignPara://将paraStack栈中的实参值一一赋给活动记录的形参位置上
			buf=t+5;
			paraT=0;
			for(k=0;k<(int)i.a;k++)
			{
				s[buf]=paraStack[k];
				buf++;
			}
			break;
		case Cal://过程函数调用
			s[t+1]=base(i.l);//动态链
			s[t+2]=b;//静态链
			s[t+4]=p;//下条语句地址
			b=t+1;
			p=(int)i.a;
			break;
		case Int://分配空间
			t=t+(int)i.a;
			break;
		case Jmp://无条件跳转
			p=(int)i.a;
			break;
		case Jpc://有条件跳转
			if(((int)s[t])==0)
			{
				p=(int)i.a;
				t--;
			}
			break;
		case RedI://读入integer型数据
			scanf("%d",&tempI);
			s[base(i.l)+(int)i.a]=tempI;
			break;
		case RedR://读入real型数据
			scanf("%f",&tempR);
			s[base(i.l)+(int)i.a]=tempR;
			break;
		case RedC://读入char型数据
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
		case LodRet://将函数的返回值保存到中间变量FuncReturn中
			t++;
			s[t]=FuncReturn;
			break;
		case StoRet://把存在FuncReturn中的值放到栈顶，用于下一步的操作
			FuncReturn=s[t];
			t--;
			break;
		case LodAdd://把实参的地址放到栈顶
			t++;
			s[t]=base(i.l)+(int)i.a;
			break;
		case LDA://间接寻址
			t++;
			s[t]=s[(int)s[base(i.l)+(int)(i.a)]];
			break;
		case StoA://间接存
			s[(int)s[base(i.l)+(int)(i.a)]]=s[t];
			t--;
			break;
		case Template://载入数组模板，进行动态检查
			if(s[t]>=i.a||s[t]<0)
			{
				printf("RuntimeError:数组下标越界！\n");
				return;
			}
			break;
		default:
			break;
		}
	}while(p!=0);
}

/*通过静态链查找，找l次，l是层次差*/
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
/*打印出来所有的指令*/
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

/*打印符号表至tableInfo.txt*/
void printTableInfo()
{
	int i;
	tableOut=fopen("TableInfo.txt","w");
	for(i=1;i<=tableindex;i++)
		fprintf(tableOut,"name:%s\t type:%d\t kind:%d\t level:%d\t address:%d\n",Table[i].name,Table[i].type
		,Table[i].kind,Table[i].level,Table[i].address);
	fclose(tableOut);
}
/* <分程序>::=[<常量说明部分>][<变量说明部分>]{[<过程说明部分>]| [<函数说明部分>]}<复合语句>*/
void block(int level,int *address)
{
	int cx0=codeindex;
	int tx0;
	int add=4;
	int constFlag=0;//用来标记常量声明和变量声明，常量声明必须在变量声明之前
	generate(Jmp,0,0);//以后返填程序入口
	do
	{	
		
		if(sym==constsym)//如果是关键字"const"，则进入常量定义子程序
		{
			if(constFlag==1)
				error(39);//常量声明必须在变量声明之前！
			Constdeclaration(level);
			while(sym==comma)//如果遇到逗号，则进入另一个常量定义
			{
				Constdeclaration(level);
			}
			if(sym==semicolon)//分号，常量声明结束
				getSym();
			else
			{
				getSym();
				error(4);//常量声明部分没有以分号结束
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
				getSym();//对于这条规则，我们预读一个符号，如果是标识符则继续，否则跳出变量说明部分
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
				error(4);//没有以分号结尾
			block(level+1,&add);
			PopTable(tx0+1,tableindex);
			if(sym==semicolon)
				getSym();
			else
				error(4);//没有以分号结尾
		}
	}while(sym==constsym||sym==varsym||sym==funcsym||sym==prosym);
	codeTable[cx0].a=codeindex;//返填跳转地址
	generate(Int,0,*address);
	SentenceBegin(level);
	generate(Opr,0,0);//return
}


void main()
{
	//在main函数中初始分配空间，分别是：SL静态链、DL动态链、函数返回值、RA返回地址
	int add=4;
	int i;
//	char fileName[40];
	char* fileName=(char*)malloc(sizeof(char)*500); 
	printf("请输入程序的名字：");
	gets(fileName);
	fileIn=fopen(fileName,"r");
	
	getSym();
	block(0,&add);

	if(sym!=period)
		error(32);

	//打印符号表
	printTableInfo();
	//打印P-code
	listcode();
	
	if(errNum==0)
		interpret();
	else
		printf("出现错误：%d 个\n",errNum);

	getchar();

	getchar();
}













