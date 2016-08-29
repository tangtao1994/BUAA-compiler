/////////////////////////////////HeadFile/////////////////////////////////////////
#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include<ctype.h>
#define MAXLINE 100                                 //����һ�����ܶ�ȡ������ַ��ĸ���
#define MAXLENGTH_NAME 100                          //������Ŀ��Խ��ܵ����ֳ���
#define RESERVENUM 22                               //���屣���ֵĸ���
static char line[MAXLINE];                          //����ÿ�ζ��ļ�����һ�еĻ�����
static int errNum=0;                                //����ERROR�ĸ���
int ll=0;                                           //����ÿ�ζ���һ�еĳ���
int cc=0;                                           //����getcʱ������ַ���
int lx=0;                                           //���嵱ǰ�����˵ڼ���
int tableindex=0;                                   //������ű�����������ǰ���ʼֵ��Ϊ1��table[0]����
int arrayindex=0;				    //���������¼�������
int constindex=0;				    //���峣����¼�������
int funcindex=0;				    //���庯����¼�������
int proindex=0;					    //������̼�¼�������
int codeindex=0;				    //����ָ��������
char currentIdent[MAXLENGTH_NAME];		    //���嵱�ڱ�ʶ��������
FILE *fileIn,*tableOut,*PcodeOut;		    //�����ļ���ָ��
char ch=' ';					    //��ȡ�ļ���ǰλ�õ��ַ�����ʼֵ����Ϊ�ո�
char buf[MAXLENGTH_NAME];			    //��������ַ��Ļ�������ֱ����ʶ��ķ���
char id[MAXLENGTH_NAME];			    //�������ĵ�ǰ��ʶ��
int INumber;					    //���嵱ǰ���������
double FNumber;					    //���嵱ǰ����ĸ�����
int step;
/*�������з��ŵ�����*/
typedef enum
{
	identsym,							//��ʶ��
	varsym,constsym,funcsym,prosym,arraysym,ifsym,elsesym,thensym,stringsym,ofsym,
	intsym,charsym,realsym,	repeatsym,untilsym,dosym,forsym,tosym,downtosym,
	beginsym,endsym,writesym,readsym,				//�������б�����
	addsym,subsym,mulsym,divsym,  					//�Ӽ��˳�
	eql,neq,lss,leq,						//���ڣ������ڣ�С�ڣ�С�ڵ���
	gtr,geq,becomes,						//���ڣ����ڵ��ڣ���ֵ
	lparen,rparen,comma,semicolon,period,colonsym,			//��С���ţ���С���ţ����ţ��ֺţ���ţ�ð��
	lbracket,rbracket,						//�������ţ���������
	squote,dquote,							//�����ţ�˫����
	intNumber,floatNumber,						//������ʵ������ͬ��intsym��realsym��
	character							//�ַ�����ͬ��charsym��
}symbol;
symbol sym;	//��ǰ�����ı�ʶ��

/*���屣���ֱ������ڴʷ�������ʱ����*/
static char reservedWord [RESERVENUM][15]={
	"var","const","integer","char","real","procedure","of",
	"if","then","else","repeat","until","do","begin","end","array",
	"to","downto","read","write","for","function"
};

/*�������Ӧ�ı����ֱ��������Ĳ��ֵ*/
static symbol reservedSym [RESERVENUM]={
	varsym,constsym,intsym,charsym,realsym,prosym,ofsym,
	ifsym,thensym,elsesym,repeatsym,untilsym,dosym,beginsym,endsym,arraysym,
	tosym,downtosym,readsym,writesym,forsym,funcsym
};

/*�����������������*/
typedef enum
{
	charkind,intkind,realkind
}varKind;


/*����ö������������P-codeָ�������*/
typedef enum
{
	Lit,Opr,Lod,Sto,Cal,Int,Jmp,Jpc,WrtI,LodArray,StoArray,RedI,RedR,RedC,StoPara,AssignPara,
	WrtR,WrtC,LodRet,StoRet,LodAdd,LDA,StoA,Template
}fct;

/*����struct�ṹ������һ��p-codeָ��Ľṹ*/
typedef struct
{
	fct f;						//P-codeָ����
	int l;						//���
	double a;					//ƫ��
}instruction;
static instruction codeTable[1000];			//����ָ���


/*�����ʾ��������*/
typedef enum
{
	varkind,constkind,prokind,funckind,parakind	//�ֱ��Ӧ�˱��������������̣���������������̵Ĳ���
}identKind;




double s[10000];				//����ջ
double paraStack[20];				//����ʵ�ε�ջ
int paraT=0;					//����ʵ��ջ��ջ��ָ��

int j;						//�м����
int t;						//ջ��ָ��
int p;						//������һ��ָ��ĵ�ַ
int b=0;					//��ǰ���еķֳ�����������Ļ���ַ
instruction i;					//��ǰҪִ�е�ָ������
/*����������ķ��ű������*/
typedef struct
{
	char name[MAXLENGTH_NAME];		//��ʶ��������
	varKind type;				//��ʶ���Ļ�������:integer,char,real
	identKind kind;				//��ʶ�������ࣺ���������������������̣������͹��̵Ĳ���
	int arrayFlag;				//�����1���ʾ������
	int AddUse;				//���õ��õı�ǣ�0��ʾ��ֵ���ã�1��ʾ����ַ
	int index; 				/* ����Ǻ�������index����������������ں�����¼���е�λ��
			   			 * ��������飬��index����������������������¼���е�λ��
						 * ����ǳ�������index����������������ڳ�����¼���е�λ��
						 * ����ǹ��̣���index����������������ڹ��̼�¼���е�λ��
						 */
	int level;				//���
	int address;				//ƫ��

}tabStruct;
static tabStruct Table [200];			//���ű�

/*�����Ӧ�ļ�¼������*/
typedef struct
{
	varKind type;				//����Ļ�������
	int len;				//����ĳ���
}arrStruct;
static arrStruct arrayTable[100];		//��������ļ�¼��

/*���峣����¼������*/
typedef struct
{
	varKind type;				//���峣��������:integer,char,real
	/*�ֱ��弸�����ͳ�����ֵ*/
	int valueI;
	char valueC;
	double valueF;
}constStruct;
constStruct constTable[100];			//���峣���ļ�¼��


/*���庯�����ͽṹ*/
typedef struct
{
	int paraNum;				//���庯���Ĳ�������
	varKind ReturnVal;			//���庯���ķ���ֵ����
}funcStruct;
funcStruct funcTable[50];			//���庯���ļ�¼��

/*������̵����ͽṹ*/
typedef struct
{
	int paraNum;				//������̵Ĳ�������
}proStruct;
proStruct proTable[50];				//������̵ļ�¼��

char ERROR_MESSAGE[50][100]={
	"ERROR0���ַ��д��ڲ��Ϸ��ַ���",
	"ERROR1���ַ�û���Ե����Ž�β�����ַ����ȳ���1��",
	"ERROR2���ַ����д��ڲ��Ϸ��ַ���",
	"ERROR3���Ƿ����ַ���",
	"ERROR4��û���ԷֺŽ�β��",
	"ERROR5����ʶ���ظ����壡",
	"ERROR6�����������г��ֲ��Ϸ��ɷ֣�",
	"ERROR7��ȱ�ٵȺţ�",
	"ERROR8�����Ǳ�ʶ�����߱�ʶ���д��ڲ��Ϸ����ţ�",
	"ERROR9�����������ж��ź���Ӧ�ø�һ����ʶ����",
	"ERROR10������ĳ���Ӧ�����޷���������",
	"ERROR11��ȱ�������ţ�",
	"ERROR12�������ڵ����ͣ�",
	"ERROR13����������������г��ֲ��Ϸ��ɷ֣�",
	"ERROR14����ʶ��δ���壡",
	"ERROR15��ȱ��С���ţ�",
	"ERROR16�������г��ֲ��Ϸ��ĳɷ֣�",
	"ERROR17�������������������ͣ�",
	"ERROR18�����������ȱ��then!",
	"ERROR19�����Ͳ�ƥ�䣡",
	"ERROR20��������г��ֲ��Ϸ��ɷ֣�",
	"ERROR21���������飡",
	"ERROR22��ȱ��end��",
	"ERROR23��ȱ��do!",
	"ERROR24�����Ǳ�����",
	"ERROR25��д����г��ֲ��Ϸ��ɷ֣�",
	"ERROR26����������ֵ��ƥ�䣡",
	"ERROR27�����Ǻ�������̣�",
	"ERROR28����������̵Ĳ���������ƥ�䣡",
	"ERROR29��ʵ���г��ֲ��Ϸ��ɷ֣�",
	"ERROR30���βκ�ʵ�ε����Ͳ�ƥ�䣡",
	"ERROR31��������ֻ�ܶԱ������У�",
	"ERROR32��ȱ�پ�ţ�",
	"ERROR33����ֵ�����ֲ��Ϸ��ɷ֣�",
	"ERROR34��ȱ�ٸ�ֵ����:=��",
	"ERROR35��charǰ�治�ܼӼ���!",
	"ERROR36��ȱ��begin��",
	"ERROR37������ַ���õ�ʵ��ֻ���Ǳ�ʶ��������Ԫ�أ�",
	"ERROR38��û���βεĺ�������̲�����С���ţ�",
	"ERROR39���������������ڱ�������֮ǰ��",
	"ERROR40��ERROR���������ͣ�",
    "ERROR41��ȱ��by��",
	"ERROR42��ȱ��to!"
	"ERROR43��ȱ��until��"

};
