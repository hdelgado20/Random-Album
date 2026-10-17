/* Disco Aleatorio - port para Nintendo 3DS (libctru + citro2d)
 * Pantalla superior: el disco que te toca. Pantalla tactil: opciones.
 * Datos en sdmc:/3ds/DiscoAleatorio/collection.txt  (artista<TAB>album<TAB>formato) */
#define _GNU_SOURCE
#include <3ds.h>
#include <citro2d.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <ctype.h>
#include <math.h>
#include <time.h>
#include <sys/stat.h>

#define RGB(r,g,b)    ((u32)(0xFF000000u|((u32)(b)<<16)|((u32)(g)<<8)|(u32)(r)))
#define RGBA(r,g,b,a) ((u32)(((u32)(a)<<24)|((u32)(b)<<16)|((u32)(g)<<8)|(u32)(r)))
#define MAXA 1000
#define LH 30.0f               /* altura de linea de la fuente del sistema a escala 1 */
#define DIR_PATH  "sdmc:/3ds/DiscoAleatorio"
#define FILE_COL  DIR_PATH "/collection.txt"
#define FILE_SET  DIR_PATH "/settings.txt"
#define NETHER 6

typedef struct { char artist[64]; char title[64]; u8 fmt; } Album;
static Album albums[MAXA];
static int nAlb = 0;

typedef struct { const char *name; u32 bgT, bgB, pan, edge, txt, dim, acc, accTxt, btn, btnTxt; } Theme;
static const Theme THEMES[7] = {
 {"Aero",        RGB(10,92,192),  RGB(143,230,230), RGB(214,234,248), RGB(255,255,255), RGB(11,47,79),    RGB(58,97,127),   RGB(47,176,30),  RGB(255,255,255), RGB(31,127,214), RGB(255,255,255)},
 {"Sunset",      RGB(74,31,122),  RGB(255,190,120), RGB(250,225,230), RGB(255,255,255), RGB(46,15,51),    RGB(106,58,98),   RGB(224,80,122), RGB(255,255,255), RGB(160,31,99),  RGB(255,255,255)},
 {"Forest",      RGB(7,68,42),    RGB(185,234,165), RGB(225,244,225), RGB(255,255,255), RGB(13,51,33),    RGB(58,104,80),   RGB(47,158,91),  RGB(255,255,255), RGB(11,107,58),  RGB(255,255,255)},
 {"Videogame",   RGB(92,148,252), RGB(92,148,252),  RGB(0,0,0),       RGB(252,252,252), RGB(252,252,252), RGB(188,188,188), RGB(0,168,0),    RGB(255,255,255), RGB(0,88,248),   RGB(255,255,255)},
 {"Underground", RGB(0,0,0),      RGB(0,0,0),       RGB(0,0,0),       RGB(255,255,255), RGB(255,255,255), RGB(200,200,200), RGB(255,255,0),  RGB(0,0,0),       RGB(255,127,39), RGB(0,0,0)},
 {"Terminal",    RGB(0,0,0),      RGB(0,20,8),      RGB(0,12,2),      RGB(0,255,65),    RGB(0,255,65),    RGB(0,192,48),    RGB(0,255,65),   RGB(0,0,0),       RGB(0,60,15),    RGB(0,255,65)},
 {"Blocky Hell", RGB(58,11,11),   RGB(150,40,10),   RGB(74,20,20),    RGB(138,58,58),   RGB(255,217,160), RGB(224,168,112), RGB(230,81,0),   RGB(255,255,255), RGB(91,30,30),   RGB(255,217,160)},
};
static const u32 FMTC[4] = { RGB(224,165,38), RGB(76,194,175), RGB(232,114,95), RGB(169,155,214) };

typedef struct {
  const char *pick,*add,*list,*theme,*lang,*back,*sort,*edit,*del,*sure,*cancel,*now,*hint,*records,*newtheme,*prev,*none,*artist,*album,*format,*langname,*full,*albc;
  const char *fmt[4]; const char *sortn[4];
} Str;
static const Str STR[2] = {
 { "Pick a random record","Add","List","Theme","Language","Back","Sort","Edit","Delete","Sure?","Cancel","Now playing","Press A to pick one","records","New theme unlocked: Blocky Hell!","Before:","No records match the filters","Artist","Album","Format","English","Collection is full","Albums: %d",
   {"Vinyl","CD","Cassette","Other"}, {"Recent","Artist","Album","Format"} },
 { "Elegir disco al azar","Anadir","Lista","Tema","Idioma","Volver","Orden","Editar","Borrar","Seguro?","Cancelar","Ahora suena","Pulsa A para elegir","discos","Nuevo tema desbloqueado: Blocky Hell!","Antes:","Ningun disco con esos filtros","Artista","Album","Formato","Espanol","La coleccion esta llena","Albumes: %d",
   {"Vinilo","CD","Casete","Otro"}, {"Recientes","Artista","Album","Formato"} },
};
static int lang = 0;
#define TX (STR[lang])

/* ---------- estado ---------- */
enum { ST_MAIN, ST_LIST, ST_ITEM, ST_FMT };
static int state = ST_MAIN, themeIdx = 0, mask = 15, netherOn = 0;
static int dispIdx = -1, pickIdx = -1, lastIdx = -1, finalIdx = -1, shuf = 0;
static float spin = 0;
static char prevTitle[64] = "";
static char toast[96] = ""; static int toastT = 0;
static int modeArtist = 0;
static int sortMode = 0, order[MAXA], nOrd = 0, scroll = 0, cur = 0, sel = -1, delArmed = 0;
static int editIdx = -1; static char tmpA[64], tmpT[64];
static C2D_TextBuf gBuf, mBuf;

/* ---------- utilidades ---------- */
static void setToast(const char *s){ snprintf(toast,sizeof toast,"%s",s); toastT = 200; }
static int containsCI(const char *h, const char *n){
  size_t ln = strlen(n);
  for(; *h; h++) if(strncasecmp(h,n,ln)==0) return 1;
  return 0;
}
static void cleanText(const char *in, char *out, size_t cap){
  size_t j = 0;
  while(*in==' ') in++;
  for(; *in && j+1<cap; in++){ char c=*in; if(c=='\t'||c=='\n'||c=='\r') c=' '; out[j++]=c; }
  while(j>0 && out[j-1]==' ') j--;
  out[j]=0;
}
static void cutUtf8(const char *s, char *out, size_t maxBytes){
  size_t n = strlen(s);
  if(n<=maxBytes){ strcpy(out,s); return; }
  size_t i = maxBytes; while(i>0 && ((unsigned char)s[i]&0xC0)==0x80) i--;
  memcpy(out,s,i); out[i]=0;
}
static int parseFmt(const char *s){
  while(*s==' ') s++;
  if(isdigit((unsigned char)*s)){ int v=atoi(s); return (v>=0&&v<=3)?v:3; }
  if(!strncasecmp(s,"vin",3)||!strncasecmp(s,"lp",2)) return 0;
  if(!strncasecmp(s,"cd",2)) return 1;
  if(!strncasecmp(s,"cas",3)||!strncasecmp(s,"tape",4)) return 2;
  return 3;
}
static void checkNether(void){
  if(netherOn) return;
  for(int i=0;i<nAlb;i++) if(containsCI(albums[i].artist,"c418")){ netherOn=1; setToast(TX.newtheme); return; }
}

/* ---------- ficheros ---------- */
static void saveAlbums(void){
  FILE *f = fopen(FILE_COL,"w"); if(!f) return;
  for(int i=0;i<nAlb;i++) fprintf(f,"%s\t%s\t%d\n",albums[i].artist,albums[i].title,albums[i].fmt);
  fclose(f);
}
static void saveSettings(void){
  FILE *f = fopen(FILE_SET,"w"); if(!f) return;
  fprintf(f,"%d %d %d %d %d\n",themeIdx,lang,mask,netherOn,modeArtist); fclose(f);
}
static void loadAll(void){
  mkdir("sdmc:/3ds",0777); mkdir(DIR_PATH,0777);
  int have = 0;
  FILE *f = fopen(FILE_SET,"r");
  if(f){ int t,l,m,n,md=0; if(fscanf(f,"%d %d %d %d %d",&t,&l,&m,&n,&md)>=4){ themeIdx=t; lang=l?1:0; mask=m&15; netherOn=n?1:0; modeArtist=md?1:0; have=1; } fclose(f); }
  if(!have){
    u8 sl; cfguInit(); if(R_SUCCEEDED(CFGU_GetSystemLanguage(&sl)) && sl==CFG_LANGUAGE_ES) lang=1; cfguExit();
  }
  if(themeIdx<0||themeIdx>NETHER||(themeIdx==NETHER&&!netherOn)) themeIdx=0;
  if(!mask) mask=15;
  f = fopen(FILE_COL,"r");
  if(f){
    char line[256];
    while(fgets(line,sizeof line,f) && nAlb<MAXA){
      line[strcspn(line,"\r\n")]=0;
      char *a=line, *t=strchr(a,'\t'); if(!t) continue; *t++=0;
      char *fm=strchr(t,'\t'); int fmt=3; if(fm){ *fm++=0; fmt=parseFmt(fm); }
      if(!*a||!*t) continue;
      snprintf(albums[nAlb].artist,64,"%s",a); snprintf(albums[nAlb].title,64,"%s",t); albums[nAlb].fmt=fmt; nAlb++;
    }
    fclose(f);
  }
  toastT = 0; toast[0]=0;
  for(int i=0;i<nAlb;i++) if(containsCI(albums[i].artist,"c418")) { if(!netherOn){ netherOn=1; saveSettings(); } break; }
}

/* ---------- orden / azar ---------- */
static int cmpIdx(const void *pa, const void *pb){
  int x=*(const int*)pa, y=*(const int*)pb, r=0;
  switch(sortMode){
    case 1: r=strcasecmp(albums[x].artist,albums[y].artist); break;
    case 2: r=strcasecmp(albums[x].title,albums[y].title); break;
    case 3: r=albums[x].fmt-albums[y].fmt; break;
  }
  if(!r) r=strcasecmp(albums[x].artist,albums[y].artist);
  if(!r) r=strcasecmp(albums[x].title,albums[y].title);
  return r;
}
static void buildOrder(void){
  nOrd = nAlb;
  if(sortMode==0){ for(int i=0;i<nAlb;i++) order[i]=nAlb-1-i; }
  else { for(int i=0;i<nAlb;i++) order[i]=i; qsort(order,nAlb,sizeof(int),cmpIdx); }
}
static int candidates(int *c, int skipLast){
  int n=0;
  for(int i=0;i<nAlb;i++) if((mask&(1<<albums[i].fmt)) && !(skipLast&&i==lastIdx)) c[n++]=i;
  return n;
}
static int sameArtist(int i,int j){ return strcasecmp(albums[i].artist,albums[j].artist)==0; }
static void artInfo(int idx,int *count,char *titles,size_t cap){
  int n=0; size_t len=0; titles[0]=0;
  for(int i=0;i<nAlb;i++) if((mask&(1<<albums[i].fmt)) && sameArtist(i,idx)){
    n++; size_t tl=strlen(albums[i].title);
    if(len+tl+4<cap){ if(len){ strcat(titles," / "); len+=3; } strcat(titles,albums[i].title); len+=tl; }
  }
  *count=n;
}
static int pickArtistIdx(void){
  int c[MAXA], n=candidates(c,0); if(!n) return -1;
  int firstOf[MAXA], nu=0;
  for(int a=0;a<n;a++){
    int dup=0;
    for(int b=0;b<nu;b++) if(sameArtist(c[a],firstOf[b])){ dup=1; break; }
    if(!dup) firstOf[nu++]=c[a];
  }
  int ok[MAXA], no=0;
  for(int b=0;b<nu;b++) if(!(nu>1 && lastIdx>=0 && lastIdx<nAlb && sameArtist(firstOf[b],lastIdx))) ok[no++]=firstOf[b];
  return ok[rand()%no];
}
static void doPick(void){
  if(shuf>0) return;
  if(modeArtist){
    int f=pickArtistIdx();
    if(f<0){ setToast(TX.none); return; }
    finalIdx=f; shuf=24; return;
  }
  int c[MAXA], n = candidates(c,1);
  if(n==0) n = candidates(c,0);
  if(n==0){ setToast(TX.none); return; }
  finalIdx = c[rand()%n]; shuf = 24;
}

/* ---------- dibujo ---------- */
static float textW(const char *s, float sc){
  C2D_Text t; float w=0,h=0;
  C2D_TextBufClear(mBuf); C2D_TextParse(&t,mBuf,s); C2D_TextGetDimensions(&t,sc,sc,&w,&h);
  return w;
}
static void drawText(const char *s, float x, float y, float sc, u32 col){
  C2D_Text t; C2D_TextParse(&t,gBuf,s); C2D_TextOptimize(&t);
  C2D_DrawText(&t,C2D_WithColor,x,y,0.0f,sc,sc,col);
}
static void drawTextCC(const char *s, float cx, float cy, float sc, u32 col){
  drawText(s, cx-textW(s,sc)/2, cy-LH*sc/2, sc, col);
}
static void rect(float x,float y,float w,float h,u32 c){ C2D_DrawRectSolid(x,y,0.0f,w,h,c); }
static void frameR(float x,float y,float w,float h,float b,u32 edge,u32 fill){ rect(x,y,w,h,edge); rect(x+b,y+b,w-2*b,h-2*b,fill); }
static void fitText(const char *s, float sc, float maxW, char *out){
  cutUtf8(s,out,60);
  if(textW(out,sc)<=maxW) return;
  size_t n = strlen(out);
  while(n>3 && textW(out,sc)>maxW-14){
    n--; while(n>0 && ((unsigned char)out[n]&0xC0)==0x80) n--;
    out[n]=0;
  }
  strcat(out,"...");
}
static int wrapLines(const char *s, float sc, float maxW, char out[][96], int maxL){
  int n=0; char cur[96]=""; const char *p=s;
  while(*p && n<maxL){
    char word[96]; int wl=0;
    while(*p==' ') p++;
    while(*p && *p!=' ' && wl<90) word[wl++]=*p++;
    word[wl]=0; if(!wl) break;
    char cand[200];
    if(cur[0]) snprintf(cand,sizeof cand,"%s %s",cur,word); else snprintf(cand,sizeof cand,"%s",word);
    if(!cur[0] || textW(cand,sc)<=maxW) snprintf(cur,sizeof cur,"%s",cand);
    else { snprintf(out[n++],96,"%s",cur); snprintf(cur,sizeof cur,"%s",word); }
  }
  if(cur[0] && n<maxL) snprintf(out[n++],96,"%s",cur);
  return n;
}
typedef struct { float x,y,w,h; } Rc;
static int hit(Rc r,int tx,int ty){ return tx>=r.x && tx<r.x+r.w && ty>=r.y && ty<r.y+r.h; }
static void button(Rc r,const char *label,u32 fill,u32 txt,u32 edge,float sc){
  frameR(r.x,r.y,r.w,r.h,2,edge,fill);
  drawTextCC(label,r.x+r.w/2,r.y+r.h/2,sc,txt);
}
static void bgGradient(const Theme *T){ C2D_DrawRectangle(0,0,0.0f,400,240,T->bgT,T->bgT,T->bgB,T->bgB); }

static void drawDisc(float cx,float cy,u32 label){
  C2D_DrawCircleSolid(cx,cy,0.0f,82,RGB(6,6,8));
  for(float r=78;r>=36;r-=6){ C2D_DrawCircleSolid(cx,cy,0.0f,r,(((int)r/6)&1)?RGB(26,26,30):RGB(10,10,12)); }
  for(int k=0;k<2;k++){
    float a=spin+k*3.14159f, a1=a-0.16f, a2=a+0.16f;
    C2D_DrawTriangle(cx,cy,RGBA(255,255,255,80), cx+78*cosf(a1),cy+78*sinf(a1),RGBA(255,255,255,0), cx+78*cosf(a2),cy+78*sinf(a2),RGBA(255,255,255,0), 0.0f);
  }
  C2D_DrawCircleSolid(cx,cy,0.0f,30,label);
  C2D_DrawCircleSolid(cx,cy,0.0f,5,RGB(235,245,255));
}

static void drawTop(void){
  const Theme *T=&THEMES[themeIdx];
  bgGradient(T);
  frameR(8,8,384,224,3,T->edge,T->pan);
  drawText(TX.now,20,13,0.5f,T->dim);
  const Album *d = (dispIdx>=0&&dispIdx<nAlb)?&albums[dispIdx]:NULL;
  drawDisc(112,128,d?FMTC[d->fmt]:T->acc);
  if(d){
    char lines[3][96]; int n=wrapLines(modeArtist?d->artist:d->title,0.7f,172,lines,3);
    float y=52;
    for(int i=0;i<n;i++){ drawText(lines[i],206,y,0.7f,T->txt); y+=LH*0.7f; }
    char tagTxt[48]; float yAfter;
    if(modeArtist){
      int cnt=0; char tl[220]; artInfo(dispIdx,&cnt,tl,sizeof tl);
      snprintf(tagTxt,sizeof tagTxt,TX.albc,cnt);
      char sub[2][96]; int m=wrapLines(tl,0.42f,172,sub,2);
      for(int k=0;k<m;k++) drawText(sub[k],206,y+6+k*LH*0.42f,0.42f,T->dim);
      yAfter=y+6+m*LH*0.42f;
    } else {
      char a[96]; fitText(d->artist,0.55f,172,a);
      drawText(a,206,y+6,0.55f,T->dim);
      yAfter=y+6+LH*0.55f;
      snprintf(tagTxt,sizeof tagTxt,"%s",TX.fmt[d->fmt]);
    }
    Rc tag={206,yAfter+8,110,22};
    frameR(tag.x,tag.y,tag.w,tag.h,2,T->edge,FMTC[d->fmt]);
    drawTextCC(tagTxt,tag.x+tag.w/2,tag.y+tag.h/2,0.5f,RGB(11,31,51));
    if(prevTitle[0] && shuf==0){
      char pv[96],pt[64]; fitText(prevTitle,0.42f,160,pt); snprintf(pv,sizeof pv,"%s %s",TX.prev,pt);
      drawText(pv,206,198,0.42f,T->dim);
    }
  } else {
    drawTextCC(TX.hint,296,128,0.55f,T->dim);
  }
  if(toastT>0){
    frameR(24,176,352,36,2,T->edge,T->acc);
    drawTextCC(toast,200,194,0.5f,T->accTxt);
  }
}

static void drawBottom(const Rc *R){
  const Theme *T=&THEMES[themeIdx];
  C2D_DrawRectangle(0,0,0.0f,320,240,T->bgT,T->bgT,T->bgB,T->bgB);
  char buf[160];
  if(state==ST_MAIN){
    frameR(6,6,308,228,3,T->edge,T->pan);
    button(R[0],TX.pick,T->acc,T->accTxt,T->edge,0.6f);
    for(int i=0;i<4;i++){
      int on = mask&(1<<i);
      button(R[1+i],TX.fmt[i],on?FMTC[i]:T->pan,on?RGB(11,31,51):T->dim,on?T->edge:T->dim,0.42f);
    }
    button(R[9],TX.album,!modeArtist?T->acc:T->pan,!modeArtist?T->accTxt:T->dim,!modeArtist?T->edge:T->dim,0.5f);
    button(R[10],TX.artist,modeArtist?T->acc:T->pan,modeArtist?T->accTxt:T->dim,modeArtist?T->edge:T->dim,0.5f);
    button(R[5],TX.add,T->btn,T->btnTxt,T->edge,0.6f);
    button(R[6],TX.list,T->btn,T->btnTxt,T->edge,0.6f);
    snprintf(buf,sizeof buf,"%s: %s",TX.theme,THEMES[themeIdx].name);
    button(R[7],buf,T->btn,T->btnTxt,T->edge,0.45f);
    snprintf(buf,sizeof buf,"%s: %s",TX.lang,TX.langname);
    button(R[8],buf,T->btn,T->btnTxt,T->edge,0.45f);
    snprintf(buf,sizeof buf,"%d %s",nAlb,TX.records);
    drawTextCC(buf,160,226,0.4f,T->dim);
  } else if(state==ST_LIST){
    frameR(4,4,312,232,3,T->edge,T->pan);
    button(R[0],TX.back,T->btn,T->btnTxt,T->edge,0.5f);
    snprintf(buf,sizeof buf,"%s: %s",TX.sort,TX.sortn[sortMode]);
    button(R[1],buf,T->btn,T->btnTxt,T->edge,0.5f);
    for(int r=0;r<6;r++){
      int oi=scroll+r; if(oi>=nOrd) break;
      int i=order[oi]; float y=46+r*31;
      frameR(10,y,300,28,2,(oi==cur)?T->acc:T->dim,T->pan);
      rect(14,y+5,10,18,FMTC[albums[i].fmt]);
      snprintf(buf,sizeof buf,"%s - %s",albums[i].artist,albums[i].title);
      char cut[96]; fitText(buf,0.45f,268,cut);
      drawText(cut,30,y+6,0.45f,T->txt);
    }
    if(nOrd==0) drawTextCC(TX.none,160,130,0.45f,T->dim);
  } else if(state==ST_ITEM && sel>=0 && sel<nAlb){
    frameR(6,6,308,228,3,T->edge,T->pan);
    char a[96]; fitText(albums[sel].artist,0.55f,280,a);
    drawTextCC(a,160,28,0.55f,T->dim);
    char lines[3][96]; int n=wrapLines(albums[sel].title,0.7f,280,lines,3);
    for(int i=0;i<n;i++) drawTextCC(lines[i],160,54+i*LH*0.7f,0.7f,T->txt);
    drawTextCC(TX.fmt[albums[sel].fmt],160,118,0.5f,T->dim);
    button(R[0],TX.edit,T->btn,T->btnTxt,T->edge,0.6f);
    button(R[1],delArmed?TX.sure:TX.del,delArmed?T->acc:T->btn,delArmed?T->accTxt:T->btnTxt,T->edge,0.6f);
    button(R[2],TX.back,T->btn,T->btnTxt,T->edge,0.55f);
  } else if(state==ST_FMT){
    frameR(6,6,308,228,3,T->edge,T->pan);
    drawTextCC(TX.format,160,26,0.65f,T->txt);
    for(int i=0;i<4;i++) button(R[i],TX.fmt[i],FMTC[i],RGB(11,31,51),T->edge,0.6f);
    button(R[4],TX.cancel,T->btn,T->btnTxt,T->edge,0.5f);
  }
}

/* ---------- teclado y flujos ---------- */
static int askText(const char *hint, const char *init, char *out, size_t cap){
  SwkbdState sw; char buf[256]; memset(buf,0,sizeof buf);
  swkbdInit(&sw,SWKBD_TYPE_NORMAL,2,60);
  swkbdSetHintText(&sw,hint);
  if(init && init[0]) swkbdSetInitialText(&sw,init);
  swkbdSetButton(&sw,SWKBD_BUTTON_LEFT,TX.cancel,false);
  swkbdSetButton(&sw,SWKBD_BUTTON_RIGHT,"OK",true);
  swkbdSetValidation(&sw,SWKBD_NOTEMPTY,0,0);
  SwkbdButton b = swkbdInputText(&sw,buf,sizeof buf);
  if(b!=SWKBD_BUTTON_RIGHT) return 0;
  cleanText(buf,out,cap);
  return out[0]!=0;
}
static void startAddOrEdit(int idx){
  char a[64], t[64];
  if(!askText(TX.artist, idx>=0?albums[idx].artist:"", a, sizeof a)) return;
  if(!askText(TX.album,  idx>=0?albums[idx].title:"",  t, sizeof t)) return;
  snprintf(tmpA,sizeof tmpA,"%s",a); snprintf(tmpT,sizeof tmpT,"%s",t);
  editIdx = idx; state = ST_FMT;
}
static void commitFmt(int fmt){
  if(editIdx>=0){
    snprintf(albums[editIdx].artist,64,"%s",tmpA); snprintf(albums[editIdx].title,64,"%s",tmpT); albums[editIdx].fmt=fmt;
    state = ST_LIST;
  } else {
    if(nAlb>=MAXA){ setToast(TX.full); state=ST_MAIN; return; }
    snprintf(albums[nAlb].artist,64,"%s",tmpA); snprintf(albums[nAlb].title,64,"%s",tmpT); albums[nAlb].fmt=fmt; nAlb++;
    state = ST_MAIN;
  }
  saveAlbums(); checkNether(); saveSettings(); buildOrder();
}
static void deleteAlbum(int i){
  memmove(&albums[i],&albums[i+1],(size_t)(nAlb-i-1)*sizeof(Album)); nAlb--;
  dispIdx=pickIdx=lastIdx=finalIdx=-1; shuf=0;
  saveAlbums(); buildOrder();
  if(cur>=nOrd) cur=nOrd>0?nOrd-1:0;
  if(scroll>cur) scroll=cur;
}
static void nextTheme(int dir){
  for(int k=0;k<7;k++){
    themeIdx=(themeIdx+dir+7)%7;
    if(themeIdx!=NETHER || netherOn) break;
  }
  saveSettings();
}
static void keepCurVisible(void){
  int maxS = nOrd>6 ? nOrd-6 : 0;
  if(cur>=nOrd) cur = nOrd>0 ? nOrd-1 : 0;
  if(cur<0) cur = 0;
  if(cur<scroll) scroll = cur;
  if(cur>scroll+5) scroll = cur-5;
  if(scroll>maxS) scroll = maxS;
  if(scroll<0) scroll = 0;
}

static void layout(Rc *R){
  if(state==ST_MAIN){
    R[0]=(Rc){20,12,280,46};
    for(int i=0;i<4;i++) R[1+i]=(Rc){20+i*71,100,65,28};
    R[5]=(Rc){20,134,137,38}; R[6]=(Rc){163,134,137,38}; R[7]=(Rc){20,178,137,38}; R[8]=(Rc){163,178,137,38};
    R[9]=(Rc){20,64,138,28}; R[10]=(Rc){162,64,138,28};
  } else if(state==ST_LIST){
    R[0]=(Rc){10,10,70,28}; R[1]=(Rc){88,10,222,28};
  } else if(state==ST_ITEM){
    R[0]=(Rc){20,140,137,40}; R[1]=(Rc){163,140,137,40}; R[2]=(Rc){20,188,280,38};
  } else {
    R[0]=(Rc){20,46,137,56}; R[1]=(Rc){163,46,137,56}; R[2]=(Rc){20,110,137,56}; R[3]=(Rc){163,110,137,56}; R[4]=(Rc){20,180,280,40};
  }
}

int main(int argc, char **argv){
  gfxInitDefault();
  C3D_Init(C3D_DEFAULT_CMDBUF_SIZE); C2D_Init(C2D_DEFAULT_MAX_OBJECTS); C2D_Prepare();
  C3D_RenderTarget *topT = C2D_CreateScreenTarget(GFX_TOP,GFX_LEFT);
  C3D_RenderTarget *botT = C2D_CreateScreenTarget(GFX_BOTTOM,GFX_LEFT);
  gBuf = C2D_TextBufNew(4096); mBuf = C2D_TextBufNew(512);
  srand((unsigned)(time(NULL) ^ (unsigned)osGetTime()));
  loadAll(); buildOrder();

  Rc R[11]; int touchStartY=0, touchLastY=0, moved=0, accum=0, startIn=0, startX=0, prevState=-1;
  while(aptMainLoop()){
    hidScanInput();
    u32 kDown=hidKeysDown(), kHeld=hidKeysHeld(), kUp=hidKeysUp();
    touchPosition tp; hidTouchRead(&tp);
    int tapped=(kDown&KEY_TOUCH)!=0, tx=tp.px, ty=tp.py;
    if(kDown&KEY_START) break;
    if(kDown&KEY_L) nextTheme(-1);
    if(kDown&KEY_R) nextTheme(1);

    if(state!=prevState){ startIn=0; moved=0; prevState=state; }
    layout(R);

    if(state==ST_MAIN){
      if(kDown&KEY_A) doPick();
      if(kDown&KEY_X) startAddOrEdit(-1);
      if(kDown&KEY_Y){ buildOrder(); cur=0; scroll=0; state=ST_LIST; }
      if(kDown&KEY_SELECT){ lang=!lang; saveSettings(); }
      if(kDown&(KEY_DLEFT|KEY_DRIGHT)){ modeArtist=!modeArtist; saveSettings(); }
      if(tapped){
        if(hit(R[0],tx,ty)) doPick();
        for(int i=0;i<4;i++) if(hit(R[1+i],tx,ty)){ mask^=(1<<i); if(!mask) mask=1<<i; saveSettings(); }
        if(hit(R[9],tx,ty)){ modeArtist=0; saveSettings(); }
        if(hit(R[10],tx,ty)){ modeArtist=1; saveSettings(); }
        if(hit(R[5],tx,ty)) startAddOrEdit(-1);
        if(hit(R[6],tx,ty)){ buildOrder(); cur=0; scroll=0; state=ST_LIST; }
        if(hit(R[7],tx,ty)) nextTheme(1);
        if(hit(R[8],tx,ty)){ lang=!lang; saveSettings(); }
      }
    } else if(state==ST_LIST){
      if(kDown&KEY_B){ state=ST_MAIN; }
      if(kDown&KEY_DDOWN){ cur++; keepCurVisible(); }
      if(kDown&KEY_DUP){ cur--; keepCurVisible(); }
      if(kDown&KEY_DRIGHT){ cur+=6; keepCurVisible(); }
      if(kDown&KEY_DLEFT){ cur-=6; keepCurVisible(); }
      if(kDown&KEY_A && nOrd>0){ sel=order[cur]; delArmed=0; state=ST_ITEM; }
      if(kDown&KEY_X){ sortMode=(sortMode+1)%4; buildOrder(); cur=0; scroll=0; }
      if(tapped){ touchStartY=touchLastY=ty; startX=tx; moved=0; accum=0; startIn=(ty>=44); }
      if((kHeld&KEY_TOUCH) && startIn){
        accum += ty-touchLastY; touchLastY=ty;
        while(accum>=31){ scroll--; accum-=31; moved=1; }
        while(accum<=-31){ scroll++; accum+=31; moved=1; }
        int maxS = nOrd>6?nOrd-6:0; if(scroll>maxS) scroll=maxS; if(scroll<0) scroll=0;
      }
      if(tapped && !startIn){
        if(hit(R[0],tx,ty)) state=ST_MAIN;
        if(hit(R[1],tx,ty)){ sortMode=(sortMode+1)%4; buildOrder(); cur=0; scroll=0; }
      }
      if((kUp&KEY_TOUCH) && startIn && !moved && startX>=10 && startX<310){
        int r=(touchStartY-46)/31, oi=scroll+r;
        if(touchStartY>=46 && r<6 && oi<nOrd){ cur=oi; sel=order[oi]; delArmed=0; state=ST_ITEM; }
      }
    } else if(state==ST_ITEM){
      if(kDown&KEY_B){ state=ST_LIST; }
      if(tapped){
        if(hit(R[0],tx,ty)) startAddOrEdit(sel);
        else if(hit(R[1],tx,ty)){
          if(delArmed){ deleteAlbum(sel); state=ST_LIST; delArmed=0; } else delArmed=1;
        }
        else if(hit(R[2],tx,ty)) state=ST_LIST;
      }
    } else if(state==ST_FMT){
      if(kDown&KEY_B){ state = (editIdx>=0)?ST_LIST:ST_MAIN; }
      if(tapped){
        for(int i=0;i<4;i++) if(hit(R[i],tx,ty)) commitFmt(i);
        if(state==ST_FMT && hit(R[4],tx,ty)) state=(editIdx>=0)?ST_LIST:ST_MAIN;
      }
    }

    /* animacion de la eleccion */
    if(shuf>0){
      shuf--;
      if(shuf>0 && shuf%3==0){ int c[MAXA], n=candidates(c,0); if(n) dispIdx=c[rand()%n]; }
      if(shuf==0){
        if(pickIdx>=0 && pickIdx<nAlb) snprintf(prevTitle,sizeof prevTitle,"%s",modeArtist?albums[pickIdx].artist:albums[pickIdx].title);
        dispIdx=pickIdx=lastIdx=finalIdx;
      }
    }
    spin += (shuf>0)?0.45f:0.03f; if(spin>6.2832f) spin-=6.2832f;
    if(toastT>0) toastT--;

    layout(R);
    C3D_FrameBegin(C3D_FRAME_SYNCDRAW);
    C2D_TextBufClear(gBuf);
    C2D_TargetClear(topT,RGB(0,0,0)); C2D_SceneBegin(topT); drawTop();
    C2D_TargetClear(botT,RGB(0,0,0)); C2D_SceneBegin(botT); drawBottom(R);
    C3D_FrameEnd(0);
  }
  saveSettings();
  C2D_TextBufDelete(gBuf); C2D_TextBufDelete(mBuf);
  C2D_Fini(); C3D_Fini(); gfxExit();
  return 0;
}
