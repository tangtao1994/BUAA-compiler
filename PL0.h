/////////////////////////////////HeadFile/////////////////////////////////////////
#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include<ctype.h>
#define MAXLINE 100                                 //定义一行所能读取的最多字符的个数
#define MAXLENGTH_NAME 100                          //定义最长的可以接受的名字长度
#define RESERVENUM 22                               //定义保留字的个数
static char line[MAXLINE];                          //定义每次读文件，读一行的缓冲区
static int errNum=0;                                //定义ERROR的个数
int ll=0;                                           //定义每次读到一行的长度
int cc=0;                                           //定义getc时读入的字符数
int lx=0;                                           //定义当前读到了第几行
int tableindex=0;                                   //定义符号表的索引，我们把起始值置为1，table[0]不用
int arrayindex=0;				    //定义数组记录表的索引
int constindex=0;				    //定义常量记录表的索引
int funcindex=0;				    //定义函数记录表的索引
int proindex=0;					    //定义过程记录表的索引
int codeindex=0;				    //定义指令表的索引
char currentIdent[MAXLENGTH_NAME];		    //定义当期标识符的名字
FILE *fileIn,*tableOut,*PcodeOut;		    //定义文件的指针
char ch=' ';					    //读取文件当前位置的字符，初始值设置为空格
char buf[MAXLENGTH_NAME];			    //定义读入字符的缓冲区，直到是识别的符号
char id[MAXLENGTH_NAME];			    //定义读入的当前标识符
int INumber;					    //定义当前读入的整数
double FNumber;					    //定义当前读入的浮点数
int step;
/*定义所有符号的意义*/
typedef enum
{
	identsym,							//标识符
	varsym,constsym,funcsym,prosym,arraysym,ifsym,elsesym,thensym,stringsym,ofsym,
	intsym,charsym,realsym,	repeatsym,untilsym,dosym,forsym,tosym,downtosym,
	beginsym,endsym,writesym,readsym,				//定义所有保留字
	addsym,subsym,mulsym,divsym,  					//加减乘除
	eql,neq,lss,leq,						//等于，不等于，小于，小于等于
	gtr,geq,becomes,						//大于，大于等于，赋值
	lparen,rparen,comma,semicolon,period,colonsym,			//左小括号，右小括号，逗号，分号，句号，冒号
	lbracket,rbracket,						//左中括号，右中括号
	squote,dquote,							//单引号，双引号
	intNumber,floatNumber,						//整数，实数（不同于intsym和realsym）
	character							//字符（不同于charsym）
}symbol;
symbol sym;	//当前读到的标识符

/*定义保留字表，用于在词法分析的时候检查*/
static char reservedWord [RESERVENUM][15]={
	"var","const","integer","char","real","procedure","of",
	"if","then","else","repeat","until","do","begin","end","array",
	"to","downto","read","write","for","function"
};

/*和上面对应的保留字表，方便后面的查表赋值*/
static symbol reservedSym [RESERVENUM]={
	varsym,constsym,intsym,charsym,realsym,prosym,ofsym,
	ifsym,thensym,elsesym,repeatsym,untilsym,dosym,beginsym,endsym,arraysym,
	tosym,downtosym,readsym,writesym,forsym,funcsym
};

/*定义基本变量的类型*/
typedef enum
{
	charkind,intkind,realkind
}varKind;


/*定义枚举类型来描述P-code指令的种类*/
typedef enum
{
	Lit,Opr,Lod,Sto,Cal,Int,Jmp,Jpc,WrtI,LodArray,StoArray,RedI,RedR,RedC,StoPara,AssignPara,
	WrtR,WrtC,LodRet,StoRet,LodAdd,LDA,StoA,Template
}fct;

/*定义struct结构来描述一个p-code指令的结构*/
typedef struct
{
	fct f;						//P-code指令名
	int l;						//层次
	double a;					//偏移
}instruction;
static instruction codeTable[1000];			//定义指令表


/*定义标示符的种类*/
typedef enum
{
	varkind,constkind,prokind,funckind,parakind	//分别对应了变量，常量，过程，函数，函数或过程的参数
}identKind;




double s[10000];				//运行栈
double paraStack[20];				//保存实参的栈
int paraT=0;					//控制实参栈的栈顶指针

int j;						//中间变量
int t;						//栈顶指针
int p;						//保存下一条指令的地址
int b=0;					//当前运行的分程序的数据区的基地址
instruction i;					//当前要执行的指令名称
/*定义最基本的符号表的类型*/
typedef struct
{
	char name[MAXLENGTH_NAME];		//标识符的名字
	varKind type;				//标识符的基本类型:integer,char,real
	identKind kind;				//标识符的种类：变量，常量，函数，过程，函数和过程的参数
	int arrayFlag;				//如果是1则表示是数组
	int AddUse;				//引用调用的标记，0表示传值调用，1表示传地址
	int index; 				/* 如果是函数，则index用来检索这个函数在函数记录表中的位置
			   			 * 如果是数组，则index用来检索这个数组在数组记录表中的位置
						 * 如果是常量，则index用来检索这个常量在常量记录表中的位置
						 * 如果是过程，则index用来检索这个过程在过程记录表中的位置
						 */
	int level;				//层次
	int address;				//偏移

}tabStruct;
static tabStruct Table [200];			//符号表

/*数组对应的记录表类型*/
typedef struct
{
	varKind type;				//数组的基本类型
	int len;				//数组的长度
}arrStruct;
static arrStruct arrayTable[100];		//定义数组的记录表

/*定义常量记录表类型*/
typedef struct
{
	varKind type;				//定义常量的类型:integer,char,real
	/*分别定义几种类型常量的值*/
	int valueI;
	char valueC;
	double valueF;
}constStruct;
constStruct constTable[100];			//定义常量的记录表


/*定义函数类型结构*/
typedef struct
{
	int paraNum;				//定义函数的参数个数
	varKind ReturnVal;			//定义函数的返回值类型
}funcStruct;
funcStruct funcTable[50];			//定义函数的记录表

/*定义过程的类型结构*/
typedef struct
{
	int paraNum;				//定义过程的参数个数
}proStruct;
proStruct proTable[50];				//定义过程的记录表

char ERROR_MESSAGE[50][100]={
	"ERROR0：字符中存在不合法字符！",
	"ERROR1：字符没有以单引号结尾或者字符长度超过1！",
	"ERROR2：字符串中存在不合法字符！",
	"ERROR3：非法的字符！",
	"ERROR4：没有以分号结尾！",
	"ERROR5：标识符重复定义！",
	"ERROR6：常量定义中出现不合法成分！",
	"ERROR7：缺少等号！",
	"ERROR8：不是标识符或者标识符中存在不合法符号！",
	"ERROR9：变量定义中逗号后面应该跟一个标识符！",
	"ERROR10：数组的长度应该是无符号整数！",
	"ERROR11：缺少中括号！",
	"ERROR12：不存在的类型！",
	"ERROR13：函数或过程声明中出现不合法成分！",
	"ERROR14：标识符未定义！",
	"ERROR15：缺少小括号！",
	"ERROR16：因子中出现不合法的成分！",
	"ERROR17：数组索引必须是整型！",
	"ERROR18：条件语句中缺少then!",
	"ERROR19：类型不匹配！",
	"ERROR20：读语句中出现不合法成分！",
	"ERROR21：不是数组！",
	"ERROR22：缺少end！",
	"ERROR23：缺少do!",
	"ERROR24：不是变量！",
	"ERROR25：写语句中出现不合法成分！",
	"ERROR26：函数返回值不匹配！",
	"ERROR27：不是函数或过程！",
	"ERROR28：函数或过程的参数个数不匹配！",
	"ERROR29：实参中出现不合法成分！",
	"ERROR30：形参和实参的类型不匹配！",
	"ERROR31：读操作只能对变量进行！",
	"ERROR32：缺少句号！",
	"ERROR33：赋值语句出现不合法成分！",
	"ERROR34：缺少赋值符号:=！",
	"ERROR35：char前面不能加减号!",
	"ERROR36：缺少begin！",
	"ERROR37：传地址调用的实参只能是标识符或数组元素！",
	"ERROR38：没有形参的函数或过程不能有小括号！",
	"ERROR39：常量声明必须在变量声明之前！",
	"ERROR40：ERROR的数据类型！",
    "ERROR41：缺少by！",
	"ERROR42：缺少to!"
	"ERROR43：缺少until！"

};
